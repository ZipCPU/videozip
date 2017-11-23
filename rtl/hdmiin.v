////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmiin.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To coordinate all of the processing of an HDMI input signal,
//		from receiption, through synchronization and copying to memory.
//
//
//	Registers
//	 0	Frame address,
//			null address detect (don't write w/o address),
//			frame write fifo overflow
//	 1	miny, minx
//	 2	ny, nx	// The product determines the maximum frame size
//
//	 4	auto-sync control
//	 5	manual-sync control
//	 6	auto-sync-status
//	 7	auto-sync-quality-feedback
//
//	 8	Frame Rate
//	 9	Pixel rate
//	10	Line rate
//	12	x total, x columns
//	13	y total, y columns
//	14	h sync start, y sync start
//	15	h sync end, y sync end
//
//	Interrupts
//	   1	New frame start
//
//	Logic
//	raw -> IDELAY -> ISERDESE -> HDMIIN
//					delaycontrol
//					   -> bitslip
//					      -> decode
//					         -> synch
//					            -> memory
//					         -> mode-detect
//				[ getpixel (external) ]...not necessary any more
//				wbscope  (external)
//				EDID     (external)
//				CEC      (external)
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module	hdmiin(i_wb_clk, i_pix_clk, i_ck_pps,
		i_delay_actual_r,
		i_delay_actual_g,
		i_delay_actual_b,
		o_delay,
		i_r, i_g, i_b,
		// Control interface
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_ack, o_wb_stall, o_wb_data,
		// Bus-master, pixel writing interface
		o_pix_cyc, o_pix_stb, o_pix_we, o_pix_addr,
			o_pix_data, o_pix_sel,
			i_pix_ack, i_pix_stall, i_pix_err,
		o_vsync_int,
		o_copy_pixels,
		o_dbg_scope);
	parameter	AW=25; // Memory address width, log # of 128 bit words
	parameter	XBITS=13, YBITS=11;
	input	wire		i_wb_clk, i_pix_clk, i_ck_pps;
	// Delay control feedback inputs
	input	wire	[4:0]	i_delay_actual_r,
				i_delay_actual_g,
				i_delay_actual_b;
	output	reg	[4:0]	o_delay;
	//
	input	wire	[9:0]	i_r, i_g, i_b;
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[3:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	input	wire	[3:0]	i_wb_sel;
	output	reg		o_wb_ack;
	output	wire		o_wb_stall;
	output	reg	[31:0]	o_wb_data;
	//
	output	wire			o_pix_cyc, o_pix_stb, o_pix_we;
	output	wire	[(AW-1):0]	o_pix_addr;
	output	wire	[127:0]		o_pix_data;
	output	wire	[15:0]		o_pix_sel;
	input	wire			i_pix_ack, i_pix_stall,
					i_pix_err;
	//
	output	wire		o_vsync_int;
	output	reg	[29:0]	o_copy_pixels;
	output	wire	[31:0]	o_dbg_scope;

	assign	o_vsync_int = 1'b0;

	reg			r_write_en;
	reg			r_auto_sync_reset;
	reg			r_use_autosync, r_copy_decoded;
	reg	[(AW-1):0]	r_frame_address,
				r_words_per_line;
	reg	[4:0]		r_logic_bitslip_r,
				r_logic_bitslip_g,
				r_logic_bitslip_b;
	reg	[15:0]		r_first_xpos, r_first_ypos, r_pix_pline,
				r_nlines;

	wire	[31:0]	w_pixclocks;
	clkcounter	pixclk(i_wb_clk, i_ck_pps, i_pix_clk, w_pixclocks);

	wire	pix_auto_sync_reset;

	initial	r_write_en   = 0;
	initial	r_frame_address = 0;
	initial	r_first_xpos = 0;
	initial	r_first_ypos = 0;
	initial	r_pix_pline  = 1920;
	initial	r_nlines     = 1080;
	initial	r_words_per_line = 1920*4/16;
	initial	r_use_autosync = 1'b1;
	initial	r_copy_decoded = 1'b0;
	always @(posedge i_wb_clk)
	begin
		r_auto_sync_reset <= 1'b0;

		if ((i_wb_stb)&&(i_wb_we)) case(i_wb_addr)
		4'h0:	{ r_frame_address, r_write_en }
					<= { i_wb_data[28:4], i_wb_data[0] };
		4'h1:	{ r_first_xpos, r_first_ypos } <= i_wb_data;
		4'h2:	{ r_pix_pline,  r_nlines }     <= i_wb_data;
		4'h3:	r_words_per_line[(AW-1):0]     <= i_wb_data[(AW+4-1):4];
		4'h4:	begin // Automatic bitsync control
			if (i_wb_sel[3])
			begin
				r_auto_sync_reset <=  i_wb_data[31];
				r_use_autosync    <= !i_wb_data[30];
				r_copy_decoded    <=  i_wb_data[29];
			end
			if (i_wb_sel[0])
				o_delay <= i_wb_data[4:0];
			end
		4'h5:	begin // Manual bitsync control
			r_use_autosync   <= 1'b0;
			r_auto_sync_reset <= (|i_wb_sel[2:0]);
			if (i_wb_sel[2])
				r_logic_bitslip_r <= i_wb_data[20:16];
			if (i_wb_sel[1])
				r_logic_bitslip_g <= i_wb_data[12: 8];
			if (i_wb_sel[0])
				r_logic_bitslip_b <= i_wb_data[ 4: 0];
			end
		/*
		4'hc:	o_wb_data <= { wh_total, wh_npix   };
		4'hd:	o_wb_data <= { wv_total, wv_nlines };
		4'he:	o_wb_data <= { wh_sstart, wh_ssend };
		4'hf:	o_wb_data <= { wv_sstart, wv_ssend };
		*/
		default: begin end
		endcase

		if (i_pix_err)
			r_write_en <= 1'b0;
	end

	transferstb	syncreset(i_wb_clk, i_pix_clk, r_auto_sync_reset,
				pix_auto_sync_reset);

	wire	[31:0]	w_manual_sync_word, w_automatic_sync_word,
			w_quality_sync_word;
	wire	[9:0]	syncd_r, syncd_g, syncd_b;

	hdmisync insync(i_pix_clk,
			pix_auto_sync_reset,
			r_use_autosync,
			r_logic_bitslip_r,
			r_logic_bitslip_g,
			r_logic_bitslip_b,
			i_r, i_g, i_b,
			syncd_r, syncd_g, syncd_b,
			w_manual_sync_word,
			w_automatic_sync_word,
			w_quality_sync_word);

	wire		w_pvr, w_pvg, w_pvb;
	wire	[1:0]	dsync, w_ign_r, w_ign_g;
	wire	[7:0]	dpix_r, dpix_g, dpix_b;
	wire	[5:0]	apix_r, apix_g, apix_b;

	tmdsdecode	tmdsr(i_pix_clk, syncd_r, w_pvr, { apix_r, dpix_r }, w_ign_r);
	tmdsdecode	tmdsg(i_pix_clk, syncd_g, w_pvg, { apix_g, dpix_g }, w_ign_g);
	tmdsdecode	tmdsb(i_pix_clk, syncd_b, w_pvb, { apix_b, dpix_b }, dsync);

	//
	//
	reg		sync_now;
	reg	[10:0]	sync_reg;
	initial	sync_reg = 0;
	always @(posedge i_pix_clk)
		sync_reg <= { sync_reg[9:0],
			((!w_pvr)&&(!apix_r[4])
				&&(!w_pvg)&&(!apix_g[4])
				&&(!w_pvb)&&(!apix_b[4])) };
	initial	sync_now = 1'b0;
	always @(posedge i_pix_clk)
		sync_now <= (sync_reg[10:0] == 11'h7ff);


	//
	//
	reg		vguard_now;
	reg	[1:0]	pre_vguard;
	always @(posedge i_pix_clk)
		pre_vguard[1] <= pre_vguard[0];
	always @(posedge i_pix_clk)
		pre_vguard[0] <=  (!w_pvr)&&(apix_r[5])&&(!apix_r[0])	// 0x2cc
				&&(!w_pvg)&&(apix_g[5])&&( apix_g[0])	// 0x133
				&&(!w_pvb)&&(apix_b[5])&&(!apix_b[0]);	// 0x2cc
	always @(posedge i_pix_clk)
		vguard_now <= (pre_vguard==2'b11);

	//
	//
	reg		dguard_now;
	reg	[1:0]	pre_dguard;
	always @(posedge i_pix_clk)
		pre_dguard[1] <= pre_dguard[0];
	always @(posedge i_pix_clk)
		pre_dguard[0] <=  (!w_pvr)&&(apix_r[5])&&(apix_r[0])	// 0x133
				&&(!w_pvg)&&(apix_g[5])&&(apix_g[0]);	// 0x133
	always @(posedge i_pix_clk)
		dguard_now <= (pre_dguard == 2'b11);

	localparam	[1:0]	HDMI_CTL_STATE     = 2'b00;
	localparam	[1:0]	HDMI_DATA_ISLAND   = 2'b01;
	localparam	[1:0]	HDMI_VIDEO_DATA    = 2'b10;
	localparam	[1:0]	HDMI_UNKNOWN_STATE = 2'b11;

	// CLOCK 0
	//	apix,dpix
	// CLOCK 1
	//	*_.guard[0] =
	// CLOCK 2
	//	_now =
	// CLOCK 3
	//	state
	//	pv
	//	pixel_now
	//

	localparam	PIXEL_DELAY = 2;
	localparam	PIXEL_DELAY_WIDTH = 8*3+2;
	localparam	PDW = PIXEL_DELAY_WIDTH;
	reg				pixvalid;
	wire	[PDW-1:0]		pixel_now;
	generate
	if (PIXEL_DELAY > 0)
	begin
		reg	[(PIXEL_DELAY*PDW-1):0]		pixel_pipe;

		if (PIXEL_DELAY > 1)
		begin
			always @(posedge i_pix_clk)
				pixel_pipe <= {
					pixel_pipe[(PIXEL_DELAY-1)*PDW-1:0],
					dsync,dpix_r,dpix_g,dpix_b
					};

			assign	pixel_now = pixel_pipe[((PIXEL_DELAY)*PDW-1)
						:((PIXEL_DELAY-1)*PDW)];
		end else begin
			always @(posedge i_pix_clk)
				pixel_pipe <= { dsync,dpix_r,dpix_g,dpix_b };

			assign	pixel_now = pixel_pipe;
		end

	end else
		assign	pixel_now = { dsync, dpix_r, dpix_g, dpix_b };
	endgenerate


	reg	[1:0]	state;
	reg	[4:0]	island_counter;
	initial	island_counter = 5'h0;
	always @(posedge i_pix_clk)
	begin
		if (sync_now)
		begin
			state <= HDMI_CTL_STATE;
			pixvalid <= 1'b0;
		end else if (vguard_now)
		begin
			state <= HDMI_VIDEO_DATA;
			pixvalid <= 1'b1;
		end else if ((!pixvalid)&&(dguard_now))
		begin
			state <= HDMI_DATA_ISLAND;
			island_counter <= 5'h1f;
			pixvalid <= 1'b0;
		end else if ((island_counter != 0)&&(state == HDMI_DATA_ISLAND))
		begin
			island_counter <= island_counter - 1'b1;
			pixvalid <= 1'b0;
		end else if (state == HDMI_DATA_ISLAND)
		begin
			state <= HDMI_CTL_STATE;
			pixvalid <= 1'b0;
		end
	end

	wire	vsync, hsync;
	assign	vsync    = (!pixvalid)&&(pixel_now[25]);
	assign	hsync    = (!pixvalid)&&(pixel_now[24]);


	//
	//
	//
	//
	wire	[15:0]	wh_npix,   wh_sstart, wh_ssend, wh_total;
	wire	[15:0]	wv_nlines, wv_sstart, wv_ssend, wv_total;

	//
	// Try and synchronize to the horizontal, to get the incoming mode line
	//
	hdmigethmode
`ifdef	VERILATOR_NOT
		#(.INITIAL_HMODE({
			16'd1920,	// Initial pixels per row
			16'd2008,	// Initial Sync start
			16'd2052,	// Initial Sync end
			16'd2200}),	// Initial # of horizontal clocks
		  .KNOWN(1'b0)
			)
`endif
		hmode(i_pix_clk, pix_auto_sync_reset, hsync, pixvalid,
				wh_npix, wh_sstart, wh_ssend, wh_total);


	//
	// Try and synchronize to the vertical, to get the incoming v-mode line
	//
	hdmigetvmode
`ifdef	VERILATOR
		#(.INITIAL_VMODE({
			16'd1080,	// Initial number of lines
			16'd1084,	// Initial sync start
			16'd1089,	// Initial sync end
			16'd1125	// Initial line intervals per frame
			}),
		  .KNOWN(1'b1))
`endif
		vmode(i_pix_clk, pix_auto_sync_reset,
				vsync, hsync, pixvalid,
				wv_nlines, wv_sstart, wv_ssend, wv_total);


	//
	//
	// Now that we know the video mode, pixels per line, lines per frame,
	// clocks per line, clocks per frame, horizontal and vsync times, etc.,
	// let's use that to figure out what pixel we are on at any given
	// point in time.
	//
	reg		syncd_pixvalid, pix_newline, pix_newframe, pix_eol,
			pix_eof, pre_eol, zeroy;
	reg	[15:0]	xloc, yloc;
	always @(posedge i_pix_clk)
	begin
		pix_newline <= 1'b0;
		pix_eol <= ((syncd_pixvalid)&&(xloc >= wh_total - 16'h02));
		if ((pix_auto_sync_reset)||(vsync)||(hsync))
		begin
			syncd_pixvalid <= 1'b0;
			xloc <= 0;
		end else if (vguard_now)
		begin
			syncd_pixvalid <= 1'b1;
			pix_newline <= 1'b1;
			xloc <= 0;
		end else if (syncd_pixvalid)
		begin
			xloc <= xloc + 1'b1;
			if (pix_eol)
			begin
				xloc <= 0;
				syncd_pixvalid <= 1'b0;
			end
		end

		pre_eol <= (xloc >= wh_total - 16'h03);
		pix_eof     <= ((syncd_pixvalid)&&(pre_eol)
					&&(yloc >= wv_total - 16'h01));
		zeroy   <= (yloc == 16'h0);
		pix_newframe <= ((vguard_now)&&(zeroy));
		if ((pix_auto_sync_reset)||(vsync))
			yloc <= 0;
		else if ((syncd_pixvalid)&&(pix_eol))
			yloc <= yloc + 1'b1;
	end

	//
	// Return our results over the wishbone bus
	always @(posedge i_wb_clk)
		if ((!i_wb_stb)||(i_wb_we))
			o_wb_data <= 32'h0;
		else case(i_wb_addr)
		4'h0:	o_wb_data <= { {(32-AW-4){1'b0}}, r_frame_address, 3'b0, r_write_en };
		4'h1:	o_wb_data <= { r_first_xpos, r_first_ypos };
		4'h2:	o_wb_data <= { r_pix_pline,  r_nlines };
		// 4'h3
		4'h4:	o_wb_data <= {
				1'b0, !r_use_autosync, r_copy_decoded,
						i_delay_actual_r,
				3'h0, i_delay_actual_g,
				3'h0, i_delay_actual_b,
				3'h0, o_delay };		// HINSYNCC
		4'h5:	o_wb_data <= w_manual_sync_word;	// HINSYNCM
		4'h6:	o_wb_data <= w_automatic_sync_word;	// HINSYNCD
		4'h7:	o_wb_data <= w_quality_sync_word;	// HINSYNCQ
		4'h8:	o_wb_data <= w_pixclocks;		// HINPIXCLK
		4'hc:	o_wb_data <= { wh_total, wh_npix   };	// HINCOLS
		4'hd:	o_wb_data <= { wv_total, wv_nlines };	// HINROWS
		4'he:	o_wb_data <= { wh_sstart, wh_ssend };	// HINHMODE
		4'hf:	o_wb_data <= { wv_sstart, wv_ssend };	// HINVMODE
		default: o_wb_data <= 32'h0;
		endcase

	always @(posedge i_wb_clk)
		o_wb_ack <= i_wb_stb;
	assign	o_wb_stall = 1'b0;

	//
	//
	//
	//
	// Copy HDMI input data to memory
	//
	//
	//
	//
	wire			xpix_write_en;
	wire	[(AW-1):0]	xpix_frame_address, xpix_words_per_line;
	wire	[(XBITS-1):0]	xpix_first_xpos, xpix_pline;
	wire	[(YBITS-1):0]	xpix_first_ypos, xpix_nlines;
	crossclkparam	#(.PW(AW+1+AW+XBITS+YBITS+XBITS+YBITS))
		xclk(i_wb_clk, i_pix_clk,
			{ r_frame_address[(AW-1):0], r_write_en,
				r_words_per_line[(AW-1):0],
				r_first_xpos[(XBITS-1):0],
				r_first_ypos[(YBITS-1):0],
				r_pix_pline[(XBITS-1):0],
				r_nlines[(YBITS-1):0] },
			{	xpix_frame_address, xpix_write_en,
				xpix_words_per_line,
				xpix_first_xpos, xpix_first_ypos,
				xpix_pline,      xpix_nlines });
	//
	hdmiincopy #(.XBITS(XBITS), .YBITS(YBITS), .AW(AW))
		copypix(i_wb_clk, i_pix_clk, !r_write_en,
			pix_eof, pix_eol, pix_newline,
				syncd_pixvalid,
				pixel_now[23:16],	// Red
				pixel_now[15: 8],	// Green
				pixel_now[ 7: 0],	// Blue
			// Bus parameters
			xpix_write_en, xpix_frame_address, xpix_words_per_line,
			xpix_first_xpos, xpix_first_ypos,
			xpix_pline,  xpix_nlines,
			wh_npix[(XBITS-1):0], wv_nlines[(YBITS-1):0],
			o_pix_cyc, o_pix_stb, o_pix_addr, o_pix_data,
				i_pix_ack, i_pix_stall, i_pix_err);
	assign	o_pix_we = 1'b1;
	assign	o_pix_sel = 16'h7777;

	//
	//  DEBUG PROCESSING
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	//
	/*
	assign	o_dbg_scope = { hsync, vsync, pixvalid, syncd_pixvalid,
				newframe, newline, eol, eof,
			dpix_r, dpix_g, dpix_b };
	*/

	// assign	o_dbg_scope = { hsync, vsync, syncd_r, syncd_g, syncd_b };
	reg	[31:0] dbg_word;
	always @(posedge i_pix_clk)
		dbg_word <= { hsync, vsync, i_r, i_g, i_b };
	assign	o_dbg_scope = dbg_word;

	// Eventually, this will be
	//	vsync, hsync, ispixel, (!ispixel)?8'h0:8'bred, 8'bgrn, 8'bblue
	//	o_copy_pixels = { vsync, hsync, w_pvr, w_pvg, w_pvb, 3'h0,
	//			dpix_r, dpix_g, dpix_b };
	always @(posedge i_pix_clk)
		if (r_copy_decoded)
			o_copy_pixels <= { i_r, i_g, i_b };
		else
			o_copy_pixels <= { syncd_r, syncd_g, syncd_b };

	// Verilator lint_off UNUSED
	wire	[14:0]	unused;
	assign	unused = { i_wb_cyc, w_ign_r, w_ign_g,
		apix_r[3:1], apix_g[3:1], apix_b[3:1], pix_newframe };
	// verilator lint_on  UNUSED
endmodule
