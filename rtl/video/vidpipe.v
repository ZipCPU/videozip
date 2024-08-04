////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/vidpipe.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
// Registers:	
//
// O/S Operations:
//	read()	- Copies either incoming or outgoing video frame data to memory
//		(if supported)
//	write()	- (If framebuffer), writes data tot he frame buffer, clipped
//		to the image size.  (Alternatively, could set the frame buffers
//		address in memory ...)  If no framebuffer is available, this
//		should generate an O/S Error
//	ioctl() - Access to all internal control registers
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype none
// }}}
module	vidpipe #(
		// {{{
		parameter	DW = 512,
		parameter	AW = 31-$clog2(DW/8),
		parameter	CLOCKFREQ_HZ = 100_000_000,
		parameter	LGDIM = 12,	// Largest raw screen size = 4095x4095
		parameter [0:0]	OPT_HDMIIN = 1'b1,
		parameter [0:0]	OPT_FRAMEBUF = 1'b1,
		parameter [0:0]	OPT_VIDCAPTURE = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk,		// System/Bus clock
		input	wire		i_reset,	// System Reset
		// Wishbone Control ports
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[9:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		//
		// }}}
		// Incoming HDMI Video (if present)
		// {{{
		input	wire		i_hdmiclk, i_altclk, i_pixclk,
		input	wire	[9:0]	i_hdmi_red, i_hdmi_grn, i_hdmi_blu,
		// }}}
		// (Wide) Wishbone DMA master
		// {{{
		output	wire			o_dma_cyc, o_dma_stb, o_dma_we,
		output	wire	[AW-1:0]	o_dma_addr,
		output	wire	[DW-1:0]	o_dma_data,
		output	wire	[DW/8-1:0]	o_dma_sel,
		input	wire			i_dma_stall,
		input	wire			i_dma_ack,
		input	wire	[DW-1:0]	i_dma_data,
		input	wire			i_dma_err,
		// }}}
		// Outgoing HDMI Video
		// {{{
		output	wire	[9:0]	o_hdmi_red, o_hdmi_grn, o_hdmi_blu,
		// }}}
		// Clock control
		// Verilator lint_off SYNCASYNCNET
		output	wire		o_pix_reset_n,
		// Verilator lint_on  SYNCASYNCNET
		input	wire		i_pxpll_locked,
		output	reg	[1:0]	o_pxclk_sel,
		output	wire	[14:0]	o_iodelay,
		input	wire	[14:0]	i_iodelay,
		output	reg		o_interrupt,
		output	reg	[31:0]	o_pixdebug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	CWID = $clog2(CLOCKFREQ_HZ);
	localparam	WBLSB = $clog2(DW/8);
	localparam	CAP_OUTPUT = 1'b1, CAP_INPUT = 1'b0;
	localparam	[4:0]	ADR_CONTROL   = 5'h00,
				ADR_HDMIFREQ  = 5'h01,
				ADR_SIFREQ    = 5'h02,
				ADR_PXFREQ    = 5'h03,
				ADR_INSIZE    = 5'h04,
				ADR_INPORCH   = 5'h05,
				ADR_INSYNC    = 5'h06,
				ADR_INRAW     = 5'h07,
				ADR_SIZE      = 5'h08,
				ADR_PORCH     = 5'h09,
				ADR_SYNC      = 5'h0a,
				ADR_RAW       = 5'h0b,
				ADR_OVLYBASE  = 5'h0c,
				ADR_OVLYSIZE  = 5'h0d,
				ADR_OVLYOFFSET= 5'h0e,
				ADR_FPS       = 5'h0f,
			//
				ADR_CAPTURE   = 5'h10,
				ADR_CAPBASE   = 5'h11,
				ADR_CAPWORDS  = 5'h12,
				ADR_CAPPOSN   = 5'h13,
				ADR_CAPSIZE   = 5'h14,
			//
				ADR_SYNCWORD  = 5'h18;
//	16. Capture control: pxcap_count, pxcap_en, pixel mode(s)
//	17. Capture base address
//	18. Capture line width in memory words, cfg_mem_words
//	19. (Capture position ... = 0,0)
//	20. (Capture height, width = out height, width)
//
//	21. Sync word (debug only)
//	22. Test #1 (Unused at present)
//	23. Test #2 (Unused at present)

	// Verilator lint_off SYNCASYNCNET
	reg		pix_reset_sys, pix_reset, pix_reset_request;
	reg	[1:0]	pix_reset_pipe;
	wire		pix_reset_n;
	// Verilator lint_on  SYNCASYNCNET

	// Video streams
	// {{{
	wire		vga_valid, vga_vsync, vga_hsync;
	wire	[7:0]	vga_red, vga_grn, vga_blu;

	wire		rx_valid, rx_ready, rx_hlast, rx_vlast;
	wire	[23:0]	rx_data;

	wire		pipe_valid, pipe_ready, pipe_hlast, pipe_vlast;
	wire	[23:0]	pipe_data;

	wire		empty_valid, empty_ready, empty_vlast, empty_hlast;
	wire	[23:0]	empty_data;

	wire		wbpx_valid, wbpx_ready, wbpx_vlast, wbpx_hlast;
	wire [23:0]	wbpx_data;

	wire		out_valid, out_ready, out_vlast, out_hlast;
	wire [23:0]	out_data;
	// }}}

	// Configuration registers
	// {{{
	wire	[1:0]		cfg_alpha;
	reg	[1:0]		cfg_alpha_sys;
	reg	[LGDIM-1:0]	cfg_mem_words,
				cfg_mem_height;// SYS clk domain
	reg	[LGDIM-1:0]	cfg_mem_width_sys;
	reg	[AW-1:0]	cfg_framebase;
	reg			cfg_ovly_enable_sys;

	//	cfg_framebase	// Base address of the frame buffer
	//	cfg_mem_words	// Bus words per line
	//	cfg_cmap_mode	// How are memory data translated to pixels?
	//	cfg_ovly_enable,
	//	cfg_ovly_hpos, cfg_ovly_vpos
	//	ovly_err
	//	[1:0]	cfg_clk_src
	// cfg_src_sel
	//	hm_width,  hm_front, hm_synch, hm_raw,
	//	vm_height, vm_front, vm_synch, vm_raw,
	//
	//	hin_width,  hin_porch, hin_synch, hin_raw,
	//	vin_height, vin_porch, vin_synch, vin_raw,
	//	in_locked

	reg	[2:0]		cfg_cmap_mode_sys;
	wire	[2:0]		cfg_cmap_mode;
	reg			cfg_src_sel_sys;
	reg	[LGDIM-1:0]	vm_raw_sys,    hm_raw_sys,
				vm_synch_sys,  hm_synch_sys,
				vm_front_sys,  hm_front_sys,
				vm_height_sys, hm_width_sys;
	reg			vm_syncpol_sys,hm_syncpol_sys;
	wire	[LGDIM-1:0]	vm_raw,    hm_raw,
				vm_synch,  hm_synch,
				vm_front,  hm_front,
				vm_height, hm_width;
	wire			vm_syncpol,hm_syncpol;
	// }}}

	wire	[LGDIM-1:0]	cfg_mem_width;
	wire	[LGDIM-1:0]	hin_width,  hin_front, hin_synch, hin_raw;
	wire	[LGDIM-1:0]	vin_height, vin_front, vin_synch, vin_raw;
	wire			in_locked;

	reg	[8:0]	frame_counter;
	reg	[7:0]	frames_per_second;

	reg	[CWID-1:0]	pps_counter;
	reg			sys_pps;
	wire	[31:0]		pixck_counts, hdmick_counts, sick_counts;

	wire			ovly_err, ovly_err_sys, in_locked_sys;
	wire	[LGDIM-1:0]	hin_width_sys,  hin_front_sys,
				hin_synch_sys,  hin_raw_sys;
	wire	[LGDIM-1:0]	vin_height_sys, vin_front_sys,
				vin_synch_sys,  vin_raw_sys;
	wire	[LGDIM-1:0]	vout_raw,    hout_raw,
				vout_synch,  hout_synch,
				vout_front,  hout_front,
				vout_height, hout_width;
	wire			vout_syncpol,hout_syncpol;
	wire			cfg_src_sel;
	wire			cfg_ovly_enable;
	wire	[LGDIM-1:0]	cfg_ovly_vpos, cfg_ovly_hpos;
	reg	[LGDIM-1:0]	cfg_ovly_vpos_sys, cfg_ovly_hpos_sys;

	wire		px2sys_valid, px2sys_ready;
	wire		ign_sys2px_valid, sys2px_ready;
	wire		ign_frame_ready;

	wire		fb_cyc, fb_stb, fb_we, fb_stall, fb_ack, fb_err;
	wire [AW-1:0]	fb_addr;
	wire [DW-1:0]	fb_data, fb_idata;
	wire [DW/8-1:0]	fb_sel;

	wire		cap_cyc, cap_stb, cap_we, cap_stall, cap_ack, cap_err;
	wire [AW-1:0]	cap_addr;
	wire [DW-1:0]	cap_data, cap_idata;
	wire [DW/8-1:0]	cap_sel;

	reg		cfg_capen, cfg_capsrc;
	reg [LGDIM-1:0]	cfg_capwords, cfg_capcount;
	reg [AW-1:0]	cfg_capbase;
	reg	[1:0]	cfg_capmode;
	wire		wbcap_done, wbcap_err;

	reg			cfg_crop_en;
	reg	[LGDIM-1:0]	cfg_crop_hpos, cfg_crop_vpos,
				cfg_crop_width, cfg_crop_height;

	wire	[23:0]	cmap_rdata;

	reg		pre_ack, cmap_ack;
	reg	[31:0]	pre_wb_data;
	wire	[31:0]	sync_word;

	wire	[14:0]	iodelay_actual_sys;
	reg	[14:0]	iodelay_request_sys;

	wire			alph_valid, alph_ready,
				alph_hlast, alph_vlast;
	wire	[26-1:0]	alph_pixel;

	reg		pxpll_locked_sys;
	reg	[1:0]	pxpll_locked_pipe;

	wire		hin_syncpol, vin_syncpol;
	wire		hin_syncpol_sys, vin_syncpol_sys;

	reg	[1:0]	dbg_sel_sys;
	wire	[1:0]	dbg_sel;
	// Verilator lint_off UNUSED
	wire	[31:0]	src_debug, tx_debug, alph_debug, pip_debug, vga_debug;
	// Verilator lint_on  UNUSED

	wire		ipkt_valid, ipkt_hdr, ipkt_last;
	wire	[7:0]	ipkt_data;

	wire		opkt_valid, opkt_ready, opkt_hdr, opkt_last;
	wire	[7:0]	opkt_data;

	reg	last_pll_locked, last_sync;
	reg	new_frame;
	wire	rx_frame_sys, new_frame_sys;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// WB Control signaling
	// {{{
	// Configurable parameters ...
	//	cfg_framebase	// Base address of the frame buffer
	//	cfg_mem_words	// Bus words per line
	//	cfg_cmap_mode	// How are memory data translated to pixels?
	//	cfg_ovly_enable,
	//	cfg_ovly_hpos, cfg_ovly_vpos
	//	ovly_err
	//	[1:0]	cfg_clk_src -> o_pxclk_sel
	// cfg_src_sel
	//	hm_width,  hm_front, hm_synch, hm_raw, hm_syncpol
	//	vm_height, vm_front, vm_synch, vm_raw, vm_syncpol
	//
	//	in_locked
// Register controls:
//	0. CONTROL: Pixel clock source, video rx and tx reset
//		CMAP mode, HDMI RX locked, Overlay error
//
//	FREQUENCY FEEDBACK
//	1. HDMIRX pixel clock frequency
//	2. Measured (not commanded) Si5324 frequency
//	3. Measured pixel clock frequency
//
//	FRAME SIZE (4 regs each)
//	4-7: Measured HDMI incoming frame size
//	8-11: Commanded outgoing frame size
//
//	12. Overlay base address
//	13. Overlay size: vertical, width
//	14. Overlay position offset
//	15. Measured incoming frame rate
//
//	16. Capture control: pxcap_count, pxcap_en, pixel mode(s)
//	17. Capture base address
//	18. Capture line width in memory words, cfg_mem_words
//	19. (Capture position ... = 0,0)
//	20. (Capture height, width = out height, width)
//
//	24. Sync word (debug only)
//	25. Test #1 (Unused at present)
//	26. Test #2 (Unused at present)
//
	always @(posedge i_clk or negedge i_pxpll_locked)
	if (!i_pxpll_locked)
		{ pxpll_locked_sys, pxpll_locked_pipe } <= 0;
	else
		{ pxpll_locked_sys, pxpll_locked_pipe }
						<= { pxpll_locked_pipe, 1'b1 };


	initial	pix_reset_sys = 1'b1;
	initial	pix_reset_request = 1'b1;
	initial	hm_syncpol_sys = 1'b1;
	initial	vm_syncpol_sys = 1'b1;
	always @(posedge i_clk)
	begin
		if (pix_reset_request)
			pix_reset_sys <= 1'b1;
		else
			pix_reset_sys <= !pxpll_locked_sys;

		if (wbcap_done || wbcap_err)
		begin
			cfg_capen <= 0;
			cfg_capcount <= 0;
		end

		if (wbcap_err)
			cfg_capbase <= 0;

		if (i_wb_stb && i_wb_we && i_wb_addr[9:5]==5'h0)
		begin
			case(i_wb_addr[4:0])
			ADR_CONTROL: begin
				// {{{
				if (i_wb_sel[0])
				begin
					cfg_src_sel_sys <= i_wb_data[6]
						&& i_wb_data[5];
					o_pxclk_sel <= i_wb_data[5:4];
					// tx_reset_sys <= i_wb_data[2];
					// rx_reset_sys <= i_wb_data[1];
					pix_reset_request <= i_wb_data[0];
					if (i_wb_data[5:4] != o_pxclk_sel)
						pix_reset_sys <= 1'b1;
					if (i_wb_data[0])
						pix_reset_sys <= 1'b1;
				end
				if (i_wb_sel[1])
				begin
					cfg_cmap_mode_sys <= i_wb_data[10:8];
					cfg_alpha_sys <= i_wb_data[15:14];
				end end
				// }}}
			// ADR_SIFREQ: begin end
			// ADR_PXFREQ: begin end
			// ADR_HDMIFREQ: begin end
			// ADR_INSIZE: begin end
			// ADR_INPORCH: begin end
			// ADR_INSYNC: begin end
			// ADR_INRAW: begin end
			ADR_SIZE: begin
				// {{{
				if (&i_wb_sel[1:0])
					hm_width_sys <= i_wb_data[0 +: LGDIM];
				if (&i_wb_sel[3:2])
					vm_height_sys<= i_wb_data[16 +: LGDIM];
				end
				// }}}
			ADR_PORCH: begin
				// {{{
				if (&i_wb_sel[1:0])
					hm_front_sys <= i_wb_data[0 +: LGDIM];
				if (&i_wb_sel[3:2])
					vm_front_sys <= i_wb_data[16 +: LGDIM];
				end
				// }}}
			ADR_SYNC: begin
				// {{{
				if (&i_wb_sel[1:0])
				begin
					hm_synch_sys <= i_wb_data[0 +: LGDIM];
					if (LGDIM < 16)
						hm_syncpol_sys <= i_wb_data[15];
				end
				if (&i_wb_sel[3:2])
				begin
					vm_synch_sys <=i_wb_data[16 +: LGDIM];
					if (LGDIM < 16)
						vm_syncpol_sys <= i_wb_data[31];
				end end
				// }}}
			ADR_RAW: begin
				// {{{
				if (&i_wb_sel[1:0])
					hm_raw_sys <= i_wb_data[0 +: LGDIM];
				if (&i_wb_sel[3:2])
					vm_raw_sys <= i_wb_data[16 +: LGDIM];
				end
				// }}}
			ADR_OVLYBASE: begin
				// {{{
				cfg_ovly_enable_sys <= (&i_wb_sel)
						&& (i_wb_data[WBLSB +: AW]!=0);
				if (&i_wb_sel)
					cfg_framebase <= i_wb_data[WBLSB +: AW];
				end
				// }}}
			ADR_OVLYSIZE: begin
				// {{{
				if (&i_wb_sel[1:0])
					// cfg_mem_words <= { {(WBLSB){1'b0}}, i_wb_data[LGDIM-1:WBLSB] };
					cfg_mem_width_sys <= i_wb_data[LGDIM-1:0];
				if (&i_wb_sel[3:2])
					cfg_mem_height <= i_wb_data[16 +: LGDIM];
				end
				// }}}
			ADR_OVLYOFFSET: begin
				// {{{
				if (&i_wb_sel[1:0])
					cfg_ovly_hpos_sys <= i_wb_data[ 0 +: LGDIM];
				if (&i_wb_sel[3:2])
					cfg_ovly_vpos_sys <= i_wb_data[16 +: LGDIM];
				end
				// }}}
			ADR_FPS: begin
				// {{{
				if (i_wb_sel[1])
					iodelay_request_sys[4:0] <= i_wb_data[ 8+:5];
				if (i_wb_sel[2])
					iodelay_request_sys[9:5] <= i_wb_data[16+:5];
				if (i_wb_sel[3])
					iodelay_request_sys[14:10]<=i_wb_data[24+:5];
				if (i_wb_sel[3])
					dbg_sel_sys <= i_wb_data[31:30];
				end
				// }}}
			ADR_CAPTURE: begin
				// {{{
				if (i_wb_sel[3])
				begin
					cfg_capmode <= i_wb_data[30:29];
					cfg_capsrc  <= i_wb_data[28];
				end
				if (&i_wb_sel[$clog2(LGDIM)-1:0])
				begin
					cfg_capen <=(i_wb_data[LGDIM-1:0] != 0)
						&&(cfg_capbase != 0);
					cfg_capcount <= i_wb_data[LGDIM-1:0];
				end end
				// }}}
			ADR_CAPBASE: begin
				// cfg_capen <= (&i_wb_sel)
				//		&& (i_wb_data[WBLSB +: AW]!=0);
				if (&i_wb_sel)
					cfg_capbase <= i_wb_data[WBLSB +: AW];;
				end
			ADR_CAPWORDS: begin
				if (&i_wb_sel)
					cfg_capwords <= i_wb_data[WBLSB +: (LGDIM-1)]
					    + ((|i_wb_data[WBLSB-1:0]) ? 1 : 0);
				end
			ADR_CAPPOSN: begin
				if (&i_wb_sel)
				begin
					cfg_crop_vpos <= i_wb_data[16 +: LGDIM];
					cfg_crop_hpos <= i_wb_data[0 +: LGDIM];
				end end
			ADR_CAPSIZE: begin
				if (&i_wb_sel)
				begin
					cfg_crop_en <= (i_wb_data[16 +: LGDIM] > 2)
						&&(i_wb_data[0 +: LGDIM] > 0);
					cfg_crop_height <= i_wb_data[16 +: LGDIM];
					cfg_crop_width <= i_wb_data[0 +: LGDIM];
				end end
			default: begin end
			endcase
		end

		if (i_reset)
		begin
			cfg_src_sel_sys <= 1'b0;
			o_pxclk_sel <= 2'b00;
			cfg_ovly_enable_sys <= 1'b0;
			cfg_framebase <= {(AW){1'b0}};

			cfg_capen   <= 1'b0;
			cfg_capmode <= 2'b11;
			cfg_capsrc  <= CAP_INPUT;
			cfg_capbase <= {(AW){1'b0}};

			pix_reset_request <= 1'b1;
			pix_reset_sys <= 1'b1;
			iodelay_request_sys <= 15'h0;
		end

		if (!OPT_VIDCAPTURE)
		begin
			cfg_capen    <= 1'b0;
			cfg_capcount <= {(LGDIM){1'b0}};
			cfg_capbase  <= 0;
			cfg_capwords  <= 0;

			cfg_crop_vpos <= 0;
			cfg_crop_hpos <= 0;
			cfg_crop_en <= 0;
			cfg_crop_height <= 0;
			cfg_crop_width <= 0;
		end
	end

	// cfg_mem_words
	// {{{
	always @(posedge i_clk)
	case(cfg_cmap_mode_sys)
	3'h0: // 1-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys +  DW    -1) /  DW;
	3'h1: // 2-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/2) -1) / (DW/2);
	3'h2: // 4-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/4) -1) / (DW/4);
	3'h3: // 4-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/4) -1) / (DW/4);
	3'h4: // 8-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/8) -1) / (DW/8);
	3'h5: // 8-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/8) -1) / (DW/8);
	3'h6: // 16-bit pixels
		cfg_mem_words <= (cfg_mem_width_sys + (DW/16)-1) / (DW/16);
	3'h7: // 24-bit pixels, using 32b at a tim
		cfg_mem_words <= (cfg_mem_width_sys + (DW/32)-1) / (DW/32);
	endcase
	// }}}

	// cmap_ack
	// {{{
	// Reading the color map takes an extra clock cyle
	always @(posedge i_clk)
		cmap_ack <= !i_wb_we && i_wb_addr[9];
	// }}}

	// o_wb_data, pre_wb_data: Bus reads
	// {{{
	always @(posedge i_clk)
	if (i_wb_stb && !i_wb_we)
	begin
		pre_wb_data <= 0;
		if (i_wb_addr[9:5] == 5'h0)
		case(i_wb_addr[4:0])
		ADR_CONTROL: begin
				pre_wb_data[10:0] <= { cfg_cmap_mode_sys,
					1'b0, cfg_src_sel_sys, o_pxclk_sel,
					2'b0, pxpll_locked_sys, pix_reset_sys };
				pre_wb_data[16] <= in_locked_sys;
				pre_wb_data[17] <= ovly_err_sys;
				pre_wb_data[18] <= px2sys_valid;
				pre_wb_data[19] <= sys2px_ready;
			end
		ADR_HDMIFREQ:	pre_wb_data <= hdmick_counts;
		ADR_SIFREQ:	pre_wb_data <= sick_counts;
		ADR_PXFREQ:	pre_wb_data <= pixck_counts;
		ADR_INSIZE: begin
			pre_wb_data[16 +: LGDIM] <= vin_height_sys;
			pre_wb_data[ 0 +: LGDIM] <= hin_width_sys;
			end
		ADR_INPORCH: begin
			pre_wb_data[16 +: LGDIM] <= vin_front_sys;
			pre_wb_data[ 0 +: LGDIM] <= hin_front_sys;
			end
		ADR_INSYNC: begin
			pre_wb_data[15] <= hin_syncpol_sys;
			pre_wb_data[31] <= vin_syncpol_sys;

			pre_wb_data[16 +: LGDIM] <= vin_synch_sys;
			pre_wb_data[ 0 +: LGDIM] <= hin_synch_sys;
			end
		ADR_INRAW: begin
			pre_wb_data[16 +: LGDIM] <= vin_raw_sys;
			pre_wb_data[ 0 +: LGDIM] <= hin_raw_sys;
			end
		ADR_SIZE: begin
			pre_wb_data[16 +: LGDIM] <= vm_height_sys;
			pre_wb_data[ 0 +: LGDIM] <= hm_width_sys;
			end
		ADR_PORCH: begin
			pre_wb_data[16 +: LGDIM] <= vm_front_sys;
			pre_wb_data[ 0 +: LGDIM] <= hm_front_sys;
			end
		ADR_SYNC: begin
			pre_wb_data[16 +: LGDIM] <= vm_synch_sys;
			pre_wb_data[ 0 +: LGDIM] <= hm_synch_sys;

			pre_wb_data[15] <= hm_syncpol_sys;
			pre_wb_data[31] <= vm_syncpol_sys;
			end
		ADR_RAW: begin
			pre_wb_data[16 +: LGDIM] <= vm_raw_sys;
			pre_wb_data[ 0 +: LGDIM] <= hm_raw_sys;
			end
		ADR_OVLYBASE: begin
			if (cfg_ovly_enable_sys)
				pre_wb_data[WBLSB +: AW] <= cfg_framebase;
			end
		ADR_OVLYSIZE: begin
			pre_wb_data[16 +: LGDIM] <= cfg_mem_height;
			pre_wb_data[ 0 +: LGDIM] <= {
					cfg_mem_width_sys[LGDIM-1:0] };
			end
		ADR_OVLYOFFSET: begin
				// {{{
				pre_wb_data[16 +: LGDIM] <= cfg_ovly_hpos_sys;
				pre_wb_data[ 0 +: LGDIM] <= cfg_ovly_vpos_sys;
				end
				// }}}
		ADR_FPS: begin
			// {{{
				pre_wb_data[7:0] <= frames_per_second;
				pre_wb_data[ 8 +: 5] <= iodelay_actual_sys[ 4: 0];
				pre_wb_data[16 +: 5] <= iodelay_actual_sys[ 9: 5];
				pre_wb_data[24 +: 5] <= iodelay_actual_sys[14:10];
				pre_wb_data[31:30] <= dbg_sel_sys;
			end
			// }}}
		ADR_CAPTURE: begin
			pre_wb_data[31] <= 1'b1;
			pre_wb_data[30:29] <= cfg_capmode;
			pre_wb_data[28] <= cfg_capsrc;
			pre_wb_data[27] <= cfg_capen;
			pre_wb_data[26] <= wbcap_done;
			pre_wb_data[27] <= wbcap_err;
			if (cfg_capen && !wbcap_done)
				pre_wb_data[LGDIM-1:0] <= cfg_capcount;
			end
		ADR_CAPBASE: begin
				pre_wb_data[WBLSB +: AW] <= cfg_capbase;
			end
		ADR_CAPWORDS: begin
				pre_wb_data[WBLSB +: LGDIM] <= cfg_capwords;
			end
		ADR_CAPPOSN: begin
				pre_wb_data[ 0 +: LGDIM] <= cfg_crop_hpos;
				pre_wb_data[16 +: LGDIM] <= cfg_crop_vpos;
			end
		ADR_CAPSIZE: begin
				if (cfg_crop_en)
				begin
				pre_wb_data[ 0 +: LGDIM] <= cfg_crop_width;
				pre_wb_data[16 +: LGDIM] <= cfg_crop_height;
				end else begin
				pre_wb_data[ 0 +: LGDIM] <= hm_width_sys;
				pre_wb_data[16 +: LGDIM] <= vm_height_sys;
				end
			end
		ADR_SYNCWORD: begin
				pre_wb_data <= sync_word;
			end
		default: begin end
		endcase
	end

	always @(posedge i_clk)
	if (pre_ack)
	begin
		if (cmap_ack)
			o_wb_data <= { 8'h0, cmap_rdata };
		else
			o_wb_data <= pre_wb_data;
	end
	// }}}

	assign	o_wb_stall = 1'b0;

	// o_wb_ack
	// {{{
	initial	{ o_wb_ack, pre_ack } = 2'b00;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		{ o_wb_ack, pre_ack } <= 2'b0;
	else
		{ o_wb_ack, pre_ack } <= { pre_ack, i_wb_stb && !o_wb_stall };
	// }}}

	// o_interrupt
	// {{{
	always @(posedge i_clk)
	if (i_reset || pix_reset_sys)
		{ last_sync, last_pll_locked } <= 2'b00;
	else begin
		last_sync <= in_locked_sys;
		last_pll_locked <= pxpll_locked_sys;
	end

	always @(posedge i_clk)
	if (i_reset)
		o_interrupt <= 1'b0;
	else begin
		o_interrupt <= 1'b0;

		if (last_pll_locked != pxpll_locked_sys)
			o_interrupt <= 1'b1;
		if (last_sync != in_locked_sys)
			o_interrupt <= 1'b1;
		if (px2sys_valid && new_frame_sys)
			o_interrupt <= 1'b1;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Video RESET
	// {{{
	// pix_reset_sys <= changed parameters, or changed clock source

	always @(posedge i_pixclk or posedge pix_reset_sys)
	if (pix_reset_sys)
		{ pix_reset, pix_reset_pipe } <= -1;
	else
		{ pix_reset, pix_reset_pipe } <= { pix_reset_pipe, 1'b0 };

	assign	pix_reset_n = !pix_reset;
	assign	o_pix_reset_n = pix_reset_n;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Convert from HDMI to an AXI (video) stream
	// {{{

	generate if (OPT_HDMIIN)
	begin : GEN_HDMIIN_TO_AXIVID
		// {{{
		// hdmi2vga: Convert first to VGA
		hdmi2vga
		u_hdmi2vga (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			.i_hdmi_red(i_hdmi_red), .i_hdmi_grn(i_hdmi_grn),
				.i_hdmi_blu(i_hdmi_blu),
			//
			.o_pix_valid(vga_valid),
			.o_vsync(vga_vsync), .o_hsync(vga_hsync),
			.o_vga_red(vga_red), .o_vga_green(vga_grn),
				.o_vga_blue(vga_blu),
			//
			.M_DI_VALID(ipkt_valid),
			.M_DI_HDR(  ipkt_hdr),
			.M_DI_DATA( ipkt_data),
			.M_DI_LAST( ipkt_last),
			//
			.o_sync_word(sync_word),
			.o_debug(vga_debug)
			// }}}
		);

		// sync2stream: VGA to AXI (video) stream
		sync2stream #(
			.OPT_TUSER_IS_SOF(1'b0), .LGDIM(LGDIM)
		) u_sync2stream (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			// The VGA input
			// {{{
			.i_pix_valid(vga_valid),
			.i_hsync(vga_hsync),
			.i_vsync(vga_vsync),
			.i_pixel({ vga_red, vga_grn, vga_blu }),
			// }}}
			// The AXI Video stream output
			// {{{
			.M_AXIS_TVALID(rx_valid), .M_AXIS_TREADY(rx_ready),
			.M_AXIS_TDATA(rx_data), .M_AXIS_TLAST(rx_vlast),
			.M_AXIS_TUSER(rx_hlast),
			// }}}
			// Video parameters
			// {{{
			.o_width(hin_width),   .o_hfront(hin_front),
			.o_hsync(hin_synch),   .o_raw_width(hin_raw),
			.o_height(vin_height), .o_vfront(vin_front),
			.o_vsync(vin_synch),   .o_raw_height(vin_raw),
			//
			.o_vsync_pol(vin_syncpol),.o_hsync_pol(hin_syncpol),
			.o_locked(in_locked)
			// }}}
			// }}}
		);

		assign	src_debug = { (rx_hlast && rx_vlast),
			(rx_hlast && rx_vlast), 2'b0,
			rx_valid, rx_ready, rx_hlast, rx_vlast,
			rx_data };
		// }}}
	end else begin : NO_GEN_AXIVID
		// {{{
		assign	rx_valid = 1'b0;
		assign	rx_data  = 24'h0;
		assign	rx_hlast = 0;
		assign	rx_vlast = 0;

		assign	hin_width  = 0;
		assign	hin_front  = 0;
		assign	hin_synch  = 0;
		assign	hin_raw    = 0;

		assign	vin_height = 0;
		assign	vin_front  = 0;
		assign	vin_synch  = 0;
		assign	vin_raw    = 0;
		//
		assign	vin_syncpol = 1'b0;
		assign	hin_syncpol = 1'b0;

		assign	in_locked  = 1'b0;
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move the image meta data to (and from) the bus clock
	// {{{
	always @(posedge i_pixclk)
	if (pix_reset)
		new_frame <= 1'b0;
	else if (!in_locked)
		new_frame <= 1'b0;
	else if (!new_frame || px2sys_ready)
		new_frame <= out_valid && out_ready && out_hlast && out_vlast;

	tfrvalue #(
		.W(LGDIM*8+5+15)
	) u_px2sys (
		// {{{
		.i_a_clk(i_pixclk), .i_a_reset_n(pix_reset_n),
		.i_a_valid(1'b1), .o_a_ready(px2sys_ready),
			.i_a_data({
				new_frame,			//  1b
				ovly_err,			//  1b
				in_locked,			//  1b
				i_iodelay,			// 15b
				vin_syncpol,hin_syncpol,	//  2b
				vin_raw,    hin_raw,		// LGDIM
				vin_synch,  hin_synch,
				vin_front,  hin_front,
				vin_height, hin_width
				}),
		//
		.i_b_clk(i_clk), .i_b_reset_n(!pix_reset_sys),
		.o_b_valid(px2sys_valid), .i_b_ready(1'b1),
			.o_b_data({
				new_frame_sys,			//  1b
				ovly_err_sys,			//  1b
				in_locked_sys,			//  1b
				iodelay_actual_sys,		// 15b
				vin_syncpol_sys,hin_syncpol_sys, //  2b
				vin_raw_sys,    hin_raw_sys,	// LGDIM
				vin_synch_sys,  hin_synch_sys,
				vin_front_sys,  hin_front_sys,
				vin_height_sys, hin_width_sys
				})
		// }}}
	);

	tfrvalue #(
		.W(LGDIM*11+3+4+15+2+2)
	) u_sys2px (
		// {{{
		.i_a_clk(i_clk), .i_a_reset_n(!pix_reset_sys),
		.i_a_valid(1'b1), .o_a_ready(sys2px_ready),
			.i_a_data({
				dbg_sel_sys,
				iodelay_request_sys,		// 15b
				cfg_ovly_enable_sys,		// 1b
				cfg_src_sel_sys,		// 1b
				cfg_alpha_sys,			// 2b
				cfg_cmap_mode_sys,		// 3b
				cfg_mem_width_sys,		// LGDIM
				cfg_ovly_hpos_sys, cfg_ovly_vpos_sys,
				vm_syncpol_sys,hm_syncpol_sys,
				vm_raw_sys,    hm_raw_sys,
				vm_synch_sys,  hm_synch_sys,
				vm_front_sys,  hm_front_sys,
				vm_height_sys, hm_width_sys
				}),
		//
		.i_b_clk(i_pixclk), .i_b_reset_n(pix_reset_n),
		.o_b_valid(ign_sys2px_valid), .i_b_ready(1'b1),
			.o_b_data({
				dbg_sel,
				o_iodelay,
				cfg_ovly_enable,
				cfg_src_sel,
				cfg_alpha,
				cfg_cmap_mode,
				cfg_mem_width,
				cfg_ovly_hpos, cfg_ovly_vpos,
				vout_syncpol,hout_syncpol,
				vout_raw,    hout_raw,
				vout_synch,  hout_synch,
				vout_front,  hout_front,
				vout_height, hout_width
				})
		// }}}
	);

	assign	hm_width  = (cfg_src_sel && OPT_HDMIIN) ? hin_width  : hout_width;
	assign	hm_front  = (cfg_src_sel && OPT_HDMIIN) ? hin_front  : hout_front;
	assign	hm_synch  = (cfg_src_sel && OPT_HDMIIN) ? hin_synch  : hout_synch;
	assign	hm_raw    = (cfg_src_sel && OPT_HDMIIN) ? hin_raw    : hout_raw;
	assign	hm_syncpol= (cfg_src_sel && OPT_HDMIIN) ? hin_syncpol: hout_syncpol;

	assign	vm_height = (cfg_src_sel && OPT_HDMIIN) ? vin_height : vout_height;
	assign	vm_front  = (cfg_src_sel && OPT_HDMIIN) ? vin_front  : vout_front;
	assign	vm_synch  = (cfg_src_sel && OPT_HDMIIN) ? vin_synch  : vout_synch;
	assign	vm_raw    = (cfg_src_sel && OPT_HDMIIN) ? vin_raw    : vout_raw;
	assign	vm_syncpol= (cfg_src_sel && OPT_HDMIIN) ? vin_syncpol: vout_syncpol;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Measure the incoming pixel clock frame rate
	// {{{

	// Generate a once per second pulse

	// sys_pps
	// {{{
	initial	pps_counter = 0;
	always @(posedge i_clk)
	if (pps_counter >= CLOCKFREQ_HZ-1)
	begin
		pps_counter <= 0;
		sys_pps <= 1;
	end else begin
		pps_counter <= pps_counter + 1;
		sys_pps <= 0;
	end
	// }}}

	// pixck_counts
	// {{{
	clkcounter #(
		.CLOCKFREQ_HZ(0)
	) u_pixclk_counter (
		.i_sys_clk(i_clk), .i_tst_clk(i_pixclk),
		.i_sys_pps(sys_pps),
		.o_sys_counts(pixck_counts)
	);
	// }}}

	// hdmick_counts
	// {{{
	clkcounter #(
		.CLOCKFREQ_HZ(0)
	) u_hdmiclk_counter (
		.i_sys_clk(i_clk), .i_tst_clk(i_hdmiclk),
		.i_sys_pps(sys_pps),
		.o_sys_counts(hdmick_counts)
	);
	// }}}

	// sick_counts
	// {{{
	clkcounter #(
		.CLOCKFREQ_HZ(0)
	) u_siclk_counter (
		.i_sys_clk(i_clk), .i_tst_clk(i_altclk),
		.i_sys_pps(sys_pps),
		.o_sys_counts(sick_counts)
	);
	// }}}

	// Measure the frame rate

	// Move new frame indicators across clock domains
	// {{{
	tfrstb
	u_new_frame (
		// {{{
		.i_a_clk(i_pixclk), .i_a_reset_n(pix_reset_n),
		.i_a_valid(rx_valid && rx_ready && rx_vlast && rx_hlast),
			.o_a_ready(ign_frame_ready),
		//
		.i_b_clk(i_clk), .i_b_reset_n(!pix_reset_sys),
		.o_b_valid(rx_frame_sys), .i_b_ready(1'b1)
		// }}}
	);
	// }}}

	// frame_counter
	// {{{
	always @(posedge i_clk)
	if (pix_reset_sys)
		frame_counter <= 0;
	else if (sys_pps)
		frame_counter <= (rx_frame_sys) ? 1:0;
	else if (rx_frame_sys && !frame_counter[8])
		frame_counter <= frame_counter + 1;
	// }}}

	// frames_per_second <= frame_counter
	// {{{
	always @(posedge i_clk)
	if (pix_reset_sys)
		frames_per_second <= 0;
	else if (sys_pps)
	begin
		frames_per_second <= frame_counter[7:0];
		// UNLESS ... our frame counter overflowed
		if (frame_counter[8])
			frames_per_second <= 8'hff;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate an empty frame
	// {{{
	localparam	[23:0]	TRANSPARENT = 24'h0;

	vid_empty #(
		.PW(24), .PIXEL(TRANSPARENT),
		.OPT_TUSER_IS_SOF(1'b0)
	) u_empty (
		// {{{
		.i_clk(i_pixclk), .i_reset(pix_reset),
		.i_width(hm_width), .i_height(vm_height),
		//
		.M_VID_VALID(empty_valid),
		.M_VID_READY(empty_ready),
		.M_VID_DATA(empty_data),
		.M_VID_LAST(empty_vlast),
		.M_VID_USER(empty_hlast)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Mux empty frame with the RX signal
	// {{{

	generate if (OPT_HDMIIN && OPT_FRAMEBUF)
	begin : GEN_SELECT_INPUT
		vid_mux #(
			.NIN(2), .LGDIM(LGDIM), .DEF_SELECT(0),
			.OPT_TUSER_IS_SOF(0)
		) u_src_mux (
			// {{{
			.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(pix_reset_n),
			//
			.S_VID_VALID({ rx_valid, empty_valid }),
			.S_VID_READY({ rx_ready, empty_ready }),
			.S_VID_DATA({  rx_data,  empty_data  }),
			.S_VID_LAST({  rx_vlast, empty_vlast }),	// VLAST
			.S_VID_USER({  rx_hlast, empty_hlast }),	// HLAST
			//
			.M_VID_VALID(pipe_valid), .M_VID_READY(pipe_ready),
			.M_VID_DATA(pipe_data),
				.M_VID_LAST(pipe_vlast), .M_VID_USER(pipe_hlast),
			//
			.i_select(cfg_src_sel)
			// }}}
		);
	end else if (OPT_HDMIIN)
	begin : GEN_ONLY_INPUT
		// {{{
		assign	pipe_valid = rx_valid;
		assign	rx_ready= pipe_ready;
		assign	pipe_data  = rx_data;
		assign	pipe_hlast = rx_hlast;
		assign	pipe_vlast = rx_vlast;
		// }}}
	end else begin : GEN_NO_SELECT
		// {{{
		assign	pipe_valid = empty_valid;
		assign	empty_ready= pipe_ready;
		assign	pipe_data  = empty_data;
		assign	pipe_hlast = empty_hlast;
		assign	pipe_vlast = empty_vlast;

		assign	rx_ready= 1'b1;
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The framebuffer-based pipeline
	generate if (OPT_FRAMEBUF)
	begin : GEN_FRAMEBUF
		// Frame buffer pipeline declarations
		// {{{
		wire		mem_valid, mem_ready, mem_vlast, mem_hlast;
		wire [DW-1:0]	mem_data;
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// wbdma: the WishBone Frame buffer
		// {{{
		////////////////////////////////////////////////////////////////
		//

		vid_wbframebuf #(
			// {{{
			.AW(AW), .DW(DW), .LGFRAME(LGDIM), .PW(DW),
			.OPT_TUSER_IS_SOF(1'b0),
			.OPT_ASYNC_CLOCKS(1'b1)
			// }}}
		) u_framebuf (
			// {{{
			.i_clk(i_clk), .i_pixclk(i_pixclk), .i_reset(pix_reset_sys),
			.i_wb_en(cfg_ovly_enable_sys),
			.i_pix_en(1'b1),
			.i_height(cfg_mem_height), .i_mem_words(cfg_mem_words),
			.i_width(cfg_mem_width_sys),
			.i_baseaddr(cfg_framebase),
			// Wishbone (DMA) bus master
			// {{{
			.o_wb_cyc(fb_cyc), .o_wb_stb(fb_stb),.o_wb_we(fb_we),
			.o_wb_addr(fb_addr),
				.o_wb_data(fb_data), .o_wb_sel(fb_sel),
			.i_wb_stall(fb_stall), .i_wb_ack(fb_ack),
				.i_wb_data(fb_idata), .i_wb_err(fb_err),
			// }}}
			// Outgoing video stream
			// {{{
			.M_VID_TVALID(mem_valid),
			.M_VID_TREADY(mem_ready),
			.M_VID_TDATA( mem_data),
			.M_VID_TLAST( mem_vlast),
			.M_VID_TUSER( mem_hlast)
			// }}}
			// }}}
		);
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// wbpix_: VidStream2Pix (for frame buffer input)
		// {{{

		vidstream2pix #(
			// {{{
			.BUS_DATA_WIDTH(DW),
			.HMODE_WIDTH(LGDIM),
			.OPT_MSB_FIRST(1'b1),
			.OPT_TUSER_IS_SOF(1'b0)
			// }}}
		) u_mem2pix (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			// Incoming video data, w/ bus-sized pixels
			// {{{
			.S_AXIS_TVALID(mem_valid),
			.S_AXIS_TREADY(mem_ready),
			.S_AXIS_TDATA(mem_data),
			.S_AXIS_TLAST(mem_vlast),
			.S_AXIS_TUSER(mem_hlast),
			// }}}
			// Outgoing video pixel data
			// {{{
			.M_AXIS_TVALID(wbpx_valid),
			.M_AXIS_TREADY(wbpx_ready),
			.M_AXIS_TDATA(wbpx_data),
			.M_AXIS_TLAST(wbpx_vlast),
			.M_AXIS_TUSER(wbpx_hlast),
			// }}}
			.i_mode(cfg_cmap_mode),
			.i_pixels_per_line(cfg_mem_width),
			// Colormap control
			// {{{
			.i_cmap_clk(i_clk),
			.i_cmap_rd(i_wb_stb && !i_wb_we && i_wb_addr[9]),
			.i_cmap_raddr(i_wb_addr[7:0]),
			.o_cmap_rdata(cmap_rdata[23:0]),
			.i_cmap_we(i_wb_stb && i_wb_we && i_wb_addr[9]),
			.i_cmap_waddr(i_wb_addr[7:0]),
			.i_cmap_wdata(i_wb_data[23:0]),
			.i_cmap_wstrb(i_wb_sel[2:0])
			// }}}
			// }}}
		);

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// Transparency
		// {{{

		// If the color == TRANSPARENT, alpha should be set to all
		// 1'b1s, cfg_alpha otherwise.

		skidbuffer #(
			.OPT_LOWPOWER(1'b0), .OPT_OUTREG(1'b1),
			.DW(28)
		) alpha_skid (
			.i_clk(i_pixclk), .i_reset(pix_reset),
			.i_valid(wbpx_valid), .o_ready(wbpx_ready),
				.i_data({ wbpx_vlast, wbpx_hlast,
					(wbpx_data == TRANSPARENT)? 2'b11
							: cfg_alpha,
					wbpx_data }),
			.o_valid(alph_valid), .i_ready(alph_ready),
			.o_data({ alph_vlast, alph_hlast, alph_pixel })
		);

		// }}}
		////////////////////////////////////////////////////////////////
		//
		// out_*: Overlay WB Frame buffer onto the (empty or RX) stream
		// {{{

		axisvoverlay #(
			// {{{
			.LGFRAME(LGDIM), .ALPHA_BITS(2),
			.OPT_TUSER_IS_SOF(1'b0),
			.OPT_LINE_BREAK(1'b1)
			// .TRANSPARENT(0) // Alpha == 0 is fully transparent
			// }}}
		) u_overlay (
			// {{{
			.ACLK(i_pixclk), .ARESETN(pix_reset_n),
			.i_enable(cfg_ovly_enable),
			.i_hpos(cfg_ovly_hpos), .i_vpos(cfg_ovly_vpos),
			.o_err(ovly_err),
			.S_PRI_TVALID(pipe_valid), .S_PRI_TREADY(pipe_ready),
				.S_PRI_TDATA(pipe_data),
				.S_PRI_TLAST(pipe_vlast),
				.S_PRI_TUSER(pipe_hlast),
			//
			.S_OVW_TVALID(alph_valid), .S_OVW_TREADY(alph_ready),
				.S_OVW_TDATA(alph_pixel),
				.S_OVW_TLAST(alph_vlast),
				.S_OVW_TUSER(alph_hlast),
			//
			.M_VID_TVALID(out_valid), .M_VID_TREADY(out_ready),
			.M_VID_TDATA(out_data),
				.M_VID_TLAST(out_vlast), .M_VID_TUSER(out_hlast)
			// }}}
		);

		assign	alph_debug = { alph_vlast && alph_hlast,
				(alph_hlast && alph_vlast),
					alph_pixel[25:24],
				alph_valid, alph_ready, alph_hlast, alph_vlast,
				alph_pixel[23:0] };

		assign	pip_debug = { pipe_vlast && pipe_hlast,
				(pipe_hlast && pipe_vlast), 2'b0,
				pipe_valid, pipe_ready, pipe_hlast, pipe_vlast,
				pipe_data };
		// }}}
	end else begin : NO_FRAMEBUF
		// {{{
		assign	fb_cyc = 1'b0;
		assign	fb_stb = 1'b0;
		assign	fb_we  = 1'b1;
		assign	fb_addr = 0;
		assign	fb_data = 0;
		assign	fb_sel  = 0;

		assign	out_valid = pipe_valid;
		assign	pipe_ready = out_ready;
		assign	out_data   = pipe_data;
		assign	out_hlast  = pipe_hlast;
		assign	out_vlast  = pipe_vlast;
		// }}}
	end endgenerate
	////////////////////////////////////////////////////////////////////////
	//
	// wbcapture: Video capture
	// {{{

	// Config:
	//	cfg_capen
	//	vm_height_sys
	//	cfg_capwords
	//	cfg_capbase
	// Feedback
	//	wbcap_err
	//	wbcap_done

	generate if (OPT_VIDCAPTURE)
	begin : GEN_VIDCAPTURE
		// Local declarations
		// {{{
		reg			pxcap_sync;
		reg	[15:0]		frame_count;
		reg			pxcap_valid, pxcap_hlast, pxcap_vlast;
		reg	[24-1:0]	pxcap_data;
		wire			pxcap_src, pxcap_en;
		wire	[LGDIM-1:0]	pxcap_count;
		wire	[1:0]		pxcap_mode;

		wire			crop_valid, crop_vlast, crop_hlast,
					crop_ready;
		wire	[24-1:0]	crop_data;

		wire			pxm_valid, pxm_vlast, pxm_hlast,
					pxm_ready;
		wire	[DW-1:0]	pxm_data;

		wire			pxcrop_en;
		wire	[LGDIM-1:0]	pxcrop_hpos, pxcrop_vpos,
					pxcrop_width, pxcrop_height;

		// Verilator lint_off UNUSED
		wire		ign_pxcap_ready, ign_captfr_valid;
		// Verilator lint_on  UNUSED
		// }}}

		tfrvalue #(
			.W(4 + 5*LGDIM)
		) u_config (
			// {{{
			.i_a_clk(i_clk), .i_a_reset_n(!pix_reset_sys),
			.i_a_valid(1'b1), .o_a_ready(sys2px_ready),
			.i_a_data({
				cfg_crop_en,
				cfg_crop_hpos, cfg_crop_vpos,
				cfg_crop_width, cfg_crop_height,
				//
				cfg_capmode, cfg_capsrc, cfg_capen, cfg_capcount
				}),
			//
			.i_b_clk(i_pixclk), .i_b_reset_n(pix_reset_n),
			.o_b_valid(ign_captfr_valid), .i_b_ready(1'b1),
				.o_b_data({
					pxcrop_en,
					pxcrop_hpos, pxcrop_vpos,
					pxcrop_width, pxcrop_height,
			//
					pxcap_mode,
					pxcap_src, pxcap_en, pxcap_count })
			// }}}
		);

		// pxcap_sync
		// {{{
		always @(posedge i_pixclk)
		if (pix_reset)
			pxcap_sync <= 1'b1;
		else if (pxcap_src == CAP_OUTPUT)
		begin
			if (out_valid && out_hlast && out_vlast)
				pxcap_sync <= 1'b1;
			else if (out_valid && !pxcap_en)
				pxcap_sync <= 1'b0;
		end else // if (pxcap_src == CAP_INPUT)
		begin
			if (pipe_valid && pipe_hlast && pipe_vlast)
				pxcap_sync <= 1'b1;
			else if (pipe_valid && !pxcap_en)
				pxcap_sync <= 1'b0;
		end
		// }}}

		// pxcap_valid
		// {{{
		always @(posedge i_pixclk)
		if (pix_reset)
			pxcap_valid <= 1'b0;
		else if (!pxcap_en || !pxcap_sync
					|| (frame_count >= pxcap_count))
			pxcap_valid <= 1'b0;
		else if (pxcap_src == CAP_OUTPUT)
			pxcap_valid <= out_valid;
		else // if (pxcap_src == CAP_INPUT)
			pxcap_valid <= pipe_valid;
		// }}}

		// pxcap_* count
		// {{{
		always @(posedge i_pixclk)
		if (pix_reset)
			frame_count <= 0;
		else if (!pxcap_en)
			frame_count <= 0;
		else if (pxcap_src == CAP_OUTPUT)
		begin
			if (frame_count < pxcap_count && out_valid && out_vlast && out_hlast)
				frame_count <= frame_count + 1;
		end else // if (pxcap_src == CAP_INPUT)
		begin
			if (frame_count < pxcap_count && pipe_valid && pipe_vlast && pipe_hlast)
				frame_count <= frame_count + 1;
		end
		// }}}

		// pxcap_* stream
		// {{{
		always @(posedge i_pixclk)
		if (pxcap_src == CAP_OUTPUT)
		begin
			pxcap_data  <= out_data;
			pxcap_hlast <= out_hlast;
			pxcap_vlast <= out_vlast && (frame_count + 1 >= pxcap_count);
		end else if (pxcap_src == CAP_INPUT)
		begin
			pxcap_data  <= pipe_data;
			pxcap_hlast <= pipe_hlast;
			pxcap_vlast <= pipe_vlast && (frame_count + 1 >= pxcap_count);
		end
		// }}}

		vid_crop #(
			.LGDIM(LGDIM), .PW(24)
		) u_crop (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			//
			.i_cfg_en(pxcrop_en),
			.i_cfg_hpos(pxcrop_hpos),
			.i_cfg_vpos(pxcrop_vpos),
			.i_cfg_width(pxcrop_width),
			.i_cfg_height(pxcrop_height),
			//
			.S_VALID(pxcap_valid),
			.S_READY(ign_pxcap_ready),
			.S_DATA(pxcap_data),
			.S_HLAST(pxcap_hlast),
			.S_VLAST(pxcap_vlast),
			//
			.M_VALID(crop_valid),
			.M_READY(crop_ready),
			.M_DATA(crop_data),
			.M_HLAST(crop_hlast),
			.M_VLAST(crop_vlast)
			// }}}
		);

		pix2stream #(
			.BUS_DATA_WIDTH(DW)
		) u_pix2memword (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			.S_AXIS_TVALID(crop_valid),
			.S_AXIS_TREADY(crop_ready),
			.S_AXIS_TDATA(crop_data),
			.S_AXIS_TLAST(crop_hlast),
			.S_AXIS_TUSER(crop_vlast),
			//
			.M_AXIS_TVALID(pxm_valid),
			.M_AXIS_TREADY(pxm_ready),
			.M_AXIS_TDATA(pxm_data),
			.M_AXIS_TLAST(pxm_hlast),
			.M_AXIS_TUSER(pxm_vlast),
			//
			.i_mode(pxcap_mode)
			// }}}
		);

		vid_wbcamera #(
			.DW(DW), .AW(AW), .PW(24), .LGFIFO(5),
			.LGFRAME(LGDIM), .OPT_ASYNC_CLOCKS(1'b1),
			.OPT_ONESHOT(1'b1)
		) u_wbcapture (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_pixclk(i_pixclk),
			// Configuration
			.i_pix_en(pxcap_en), .i_wb_en(cfg_capen),
			.o_done(wbcap_done), .o_err(wbcap_err),
			.i_height(vm_height_sys),
			.i_mem_words(cfg_capwords),
			.i_baseaddr(cfg_capbase),
			// Wishbone DMA interface
			.o_wb_cyc(cap_cyc),     .o_wb_stb(cap_stb),
			.o_wb_we(cap_we),       .o_wb_addr(cap_addr),
			.o_wb_data(cap_data),   .o_wb_sel(cap_sel),
			.i_wb_stall(cap_stall), .i_wb_ack(cap_ack),
			.i_wb_data(cap_idata),  .i_wb_err(cap_err),
			// Video input
			.S_VID_VALID(pxm_valid),
			.S_VID_READY(pxm_ready),
			.S_VID_DATA( pxm_data),
			.S_VID_HLAST(pxm_hlast),
			.S_VID_VLAST(pxm_vlast)
			// }}}
		);

	end else begin : NO_VIDCAPTURE
		assign	cap_cyc = 1'b0;
		assign	cap_stb = 1'b0;
		assign	cap_we = 1'b0;
		assign	cap_addr = {(AW){1'b0}};
		assign	cap_data = {(DW){1'b0}};
		assign	cap_sel  = {(DW/8){1'b0}};

		assign	wbcap_err  = 1'b0;
		assign	wbcap_done = 1'b0;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		// wire	unused_cap;
		// assign	unused_cap = &{ 1'b0, cfg_capsrc, cfg_capen, wbcap_count };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DMA Arbiter
	// {{{

	generate if (OPT_FRAMEBUF && OPT_VIDCAPTURE)
	begin : GEN_ARBITER
		wbmarbiter #(
			.DW(DW), .AW(AW), .NIN(2), .LGFIFO(5)
		) u_dma_arbiter (
			.i_clk(i_clk), .i_reset(i_reset),
			//
			.s_cyc({   cap_cyc,   fb_cyc   }),
			.s_stb({   cap_stb,   fb_stb   }),
			.s_we({    cap_we,    fb_we    }),
			.s_addr({  cap_addr,  fb_addr  }),
			.s_data({  cap_data,  fb_data  }),
			.s_sel({   cap_sel,   fb_sel   }),
			.s_stall({ cap_stall, fb_stall }),
			.s_ack({   cap_ack,   fb_ack   }),
			.s_idata({ cap_idata, fb_idata }),
			.s_err({   cap_err,   fb_err   }),
			//
			.m_cyc(   o_dma_cyc   ),
			.m_stb(   o_dma_stb   ),
			.m_we(    o_dma_we    ),
			.m_addr(  o_dma_addr  ),
			.m_data(  o_dma_data  ),
			.m_sel(   o_dma_sel   ),
			.m_stall( i_dma_stall ),
			.m_ack(   i_dma_ack   ),
			.m_idata( i_dma_data  ),
			.m_err(   i_dma_err   )
		);

	end else if (OPT_FRAMEBUF)
	begin : ALWAYS_FRAMEBUF
		assign	o_dma_cyc  = fb_cyc;
		assign	o_dma_stb  = fb_stb;
		assign	o_dma_we   = fb_we;
		assign	o_dma_addr = fb_addr;
		assign	o_dma_data = fb_data;
		assign	o_dma_sel  = fb_sel;

		assign	fb_stall  = i_dma_stall;
		assign	fb_ack    = i_dma_ack;
		assign	fb_idata  = i_dma_data;
		assign	fb_err    = i_dma_err;

		assign	cap_stall = i_dma_stall;
		assign	cap_ack   = i_dma_ack;
		assign	cap_idata = i_dma_data;
		assign	cap_err   = i_dma_err;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_dma;
		assign	unused_dma = &{ 1'b0, cap_cyc, cap_stb,cap_we, cap_addr,
					cap_data, cap_sel, cap_stall, cap_ack,
					cap_idata, cap_err };
		// Verilator lint_on  UNUSED
		// }}}
	end else if (OPT_VIDCAPTURE)
	begin : ALWAYS_CAPTURE
		assign	o_dma_cyc  = cap_cyc;
		assign	o_dma_stb  = cap_stb;
		assign	o_dma_we   = cap_we;
		assign	o_dma_addr = cap_addr;
		assign	o_dma_data = cap_data;
		assign	o_dma_sel  = cap_sel;

		assign	fb_stall   = i_dma_stall;
		assign	fb_ack     = i_dma_ack;
		assign	fb_idata   = i_dma_data;
		assign	fb_err     = i_dma_err;

		assign	cap_stall  = i_dma_stall;
		assign	cap_ack    = i_dma_ack;
		assign	cap_idata  = i_dma_data;
		assign	cap_err    = i_dma_err;


		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_dma;
		assign	unused_dma = &{ 1'b0, fb_cyc, fb_stb, fb_we, fb_addr,
					fb_data, fb_sel, fb_stall, fb_ack,
					fb_idata, fb_err };
		// Verilator lint_on  UNUSED
		// }}}
	end else begin : NO_DMA
		assign	o_dma_cyc  = 1'b0;
		assign	o_dma_stb  = 1'b0;
		assign	o_dma_we   = 1'b0;
		assign	o_dma_addr = {(AW){1'b0}};
		assign	o_dma_data = {(DW){1'b0}};
		assign	o_dma_sel  = {(DW/8){1'b0}};

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_dma;
		assign	unused_dma = &{ 1'b0, i_dma_stall, i_dma_ack,
					i_dma_data, i_dma_err };
		// Verilator lint_on  UNUSED
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// HDMI packet processing
	// {{{
	localparam [0:0]	OPT_DATA_ISLAND = 1'b0;

	generate if (OPT_DATA_ISLAND)
	begin : GEN_DATA_ISLAND
		// {{{
		wire		pktdec_valid, pktdec_hdr, pktdec_last;
		wire	[7:0]	pktdec_data;

		wire		di_valid, di_ready, di_last;
		wire	[7:0]	di_data;

		hdmibchdec
		u_bch_decode (
		// {{{
		.i_clk(i_pixclk), .i_reset(pix_reset),
		//
		.S_VALID(ipkt_valid),
		.S_HDR(  ipkt_hdr),
		.S_DATA( ipkt_data),
		.S_LAST( ipkt_last),
		//
		.M_VALID(pktdec_valid),
		.M_DATA( pktdec_data),
		.M_LAST( pktdec_last)
		// }}}
		);

		hdmigate #(
			.LGFLEN(6)
		) u_gate (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		.S_AXIN_VALID(pktdec_valid),
		.S_AXIN_DATA( pktdec_data),
		.S_AXIN_LAST( pktdec_last),
		//
		.M_AXIN_VALID(di_valid),
		.M_AXIN_READY(di_ready),
		.M_AXIN_DATA( di_data),
		.M_AXIN_LAST( di_last)
		// }}}
		);

		hdmigenpkt
		u_gen_pkt (
			// {{{
			.i_clk(i_pixclk), .i_reset(pix_reset),
			//
			.S_VALID(di_valid),
			.S_READY(di_ready),
			.S_DATA( di_data),
			.S_LAST( di_last),
			// .S_ABORT(1'b0),
			//
			.M_VALID(opkt_valid),
			.M_READY(opkt_ready),
			.M_HDR(  opkt_hdr),
			.M_DATA( opkt_data),
			.M_LAST( opkt_last)
			// }}}
		);

		// }}}
	end else begin : NO_DATA_ISLAND_SUPPORT
		// {{{
		assign	opkt_valid = 1'b0;
		assign	opkt_hdr   = 1'b0;
		assign	opkt_data  = 8'h0;
		assign	opkt_last  = 1'b0;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused_di;
		assign	unused_di = &{ 1'b0, opkt_ready, ipkt_valid, ipkt_hdr,
				ipkt_data, ipkt_last };
		// Verilator lint_on  UNUSED
		// }}}
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// axis2hdmi: Convert our AXI Video stream to HDMI
	// {{{

	axishdmi #(
		.HW(LGDIM), .VW(LGDIM),
		.OPT_RESYNC_ON_VLAST(1'b1)
	) genhdmi (
		// {{{
		.i_pixclk(i_pixclk), .i_reset(pix_reset),
		// Incoming AXI video stream
		// {{{
		.i_valid(out_valid), .o_ready(out_ready),
		.i_hlast(out_hlast), .i_vlast(out_vlast), .i_rgb_pix(out_data),
		// }}}
		// Incoming packet stream
		// {{{
		.i_pkt_valid(opkt_valid),
		.o_pkt_ready(opkt_ready),
		.i_pkt_hdr(  opkt_hdr),
		.i_pkt_data( opkt_data),
		.i_pkt_last( opkt_last),
		// }}}
		// Video mode information
		// {{{
		.i_hm_width(hm_width), .i_hm_porch(hm_front),
			.i_hm_synch(hm_synch), .i_hm_raw(hm_raw),
			.i_hm_syncpol(hm_syncpol),
		//
		.i_vm_height(vm_height), .i_vm_porch(vm_front),
			.i_vm_synch(vm_synch), .i_vm_raw(vm_raw),
			.i_vm_syncpol(vm_syncpol),
		// }}}
		// HDMI outputs
		.o_red(o_hdmi_red), .o_grn(o_hdmi_grn), .o_blu(o_hdmi_blu)
		// }}}
	);

	assign	tx_debug = {
			out_vlast && out_hlast, (out_hlast && out_vlast), 2'b0,	// 4b
			out_valid, out_ready, out_hlast, out_vlast,	// 4b
			out_data };					//24b
	// }}}

	always @(posedge i_pixclk)
	case(dbg_sel)
	2'b00:	o_pixdebug <= src_debug;
	2'b01:	o_pixdebug <= alph_debug;
	2'b10:	o_pixdebug <= pip_debug;
	2'b11:	o_pixdebug <= tx_debug;
	endcase

	// Keep Verilator happy
	// {{{
	wire	unused;
	assign	unused = &{ 1'b0,
			src_debug, alph_debug, pip_debug,
			ign_sys2px_valid, ign_frame_ready,
			i_wb_data };
	// }}}
endmodule
