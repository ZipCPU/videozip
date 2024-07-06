////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/vid_wbcamera.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:
//
// Enable:
//	i_pix_en (Pixel clock)
//		If dropped, the operation is stopped and cleared.  When
//		restarted, recording continues from the base address.
//	i_wb_en (Wishbone clock)
//		Drops if not (properly) configured, or following any bus
//		error.
//
//		If dropped, all writing to the bus is stopped while i_wb_en
//		is low.  This has no effect on pixel operations.  If pixels
//		arrive during this time, they'll be accepted and forwarded to
//		the WB side, where they'll be ignored.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
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
`default_nettype	none
// }}}
module	vid_wbcamera #(
		// {{{
		parameter	DW = 128,
		parameter	AW = 31 - $clog2(DW/8),
		parameter	PW = 8,
		parameter	LGFIFO = 6,
		parameter	LGFRAME = 13,
		parameter [0:0]	OPT_ONESHOT = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
`ifdef	FORMAL
		parameter [0:0]	OPT_ASYNC_CLOCKS = 1'b0
`else
		parameter [0:0]	OPT_ASYNC_CLOCKS = 1'b1
`endif
		// }}}
	) (
		// {{{
		input	wire	i_clk,
		// Verilator lint_off SYNCASYNCNET
		input	wire	i_reset,
		// Verilator lint_on  SYNCASYNCNET
		input	wire	i_pixclk,
		//
		input	wire			i_pix_en,
		input	wire			i_wb_en,
		// output	wire			o_overflow,
		output	reg			o_err,
		output	reg			o_done,
		input	wire	[LGFRAME-1:0]	i_height, i_mem_words,
		input	wire	[AW-1:0]	i_baseaddr,
		//
		output	reg			o_wb_cyc, o_wb_stb,
		output	wire			o_wb_we,
		output	reg	[AW-1:0]	o_wb_addr,
		output	reg	[DW-1:0]	o_wb_data,
		output	wire	[DW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		//
		input	wire			S_VID_VALID,
		output	wire			S_VID_READY,
		input	wire	[PW-1:0]	S_VID_DATA,
		input	wire			S_VID_HLAST,
		input	wire			S_VID_VLAST
		// }}}
	);

	// Local declarations
	// {{{
	localparam	SRWIDTH = DW + PW;
	wire			pix_reset, pix_clearing;

	wire			s_valid, s_hlast, s_vlast, s_ready;
	wire	[PW-1:0]	s_data;

	reg				sr_valid, sr_last, sr_vlast;
	reg	[SRWIDTH-1:0]		sr_data;
	wire	[SRWIDTH-1:0]		wide_sdata;
	reg	[$clog2(SRWIDTH+1)-1:0]	sr_fill;

	wire		afifo_vlast, afifo_hlast, afifo_full, afifo_empty,
				afifo_read;
	wire	[DW-1:0]	afifo_data;

	wire			sfifo_vlast, sfifo_hlast, sfifo_read,
				sfifo_empty, sfifo_full;
	wire	[DW-1:0]	sfifo_data;
	wire	[LGFIFO:0]	sfifo_fill;

	// wb_eol and wb_eof are both error conditions.
	reg			wb_eol, wb_eof, wb_clr, wb_hlast, wb_vlast,
				wb_zero, wb_syncd;
	wire			wb_done, wb_flush;
	reg	[LGFRAME-1:0]	wb_ypos, wb_word;
	reg	[AW-1:0]	line_addr;
	reg	[LGFIFO:0]	wb_outstanding;

	wire	[AW-1:0]	wide_nwords;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Move resets cross clocks
	// {{{
	generate if (OPT_ASYNC_CLOCKS)
	begin : GEN_XCLK_RESET
		reg		r_pix_reset;
		reg	[1:0]	xpix_reset;

		always @(posedge i_pixclk or posedge i_reset)
		if (i_reset)
			{ r_pix_reset, xpix_reset } <= -1;
		else
			{ r_pix_reset, xpix_reset } <= { xpix_reset, 1'b0 };

		assign	pix_reset = r_pix_reset;
	end else begin : COPY_RESET
		assign	pix_reset = i_reset;
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) Skidbuffer
	// {{{
	assign	s_valid = S_VID_VALID;
	assign	S_VID_READY = s_ready;
	assign	s_data  = S_VID_DATA;
	assign	s_hlast = S_VID_HLAST;
	assign	s_vlast = S_VID_VLAST;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pack video pixels into bus words
	// {{{

	generate if (PW != DW)
	begin : GEN_SREG
		// {{{
		always @(posedge i_pixclk)
		if (pix_reset)
		begin
			sr_valid <= 1'b0;
			sr_fill <= 0;
			{ sr_last, sr_vlast } <= 2'b00;
		end else if (pix_clearing)
		begin
			sr_valid <= 0;
			sr_fill  <= 0;
			{ sr_last, sr_vlast } <= 2'b00;
		end else if (s_valid && s_ready)
		begin
			if (sr_valid)
			begin
				// ASSUME !afifo_fill
				//	Otherwise we have an overflow error to be
				//	dealt with elsewhere.  Those errors will need
				//	to reset us.
				// Verilator lint_off WIDTH
				if (sr_fill >= DW)
					sr_fill <= sr_fill - DW + PW;
				else
					sr_fill <= PW;
				sr_valid <= 1'b0;
			end else begin
				sr_fill <= sr_fill + PW;
				sr_valid <= (sr_fill + PW) >= DW;
				// Verilator lint_on  WIDTH
			end

			{ sr_last, sr_vlast } <= 2'b00;
			if (s_hlast)
			begin
				sr_last  <= s_hlast;
				sr_vlast <= s_vlast;
			end

		end else if (sr_valid && !afifo_full)
		begin
			if (sr_fill >= DW)
				sr_fill <= sr_fill - DW;
			else
				sr_fill <= 0;
			sr_valid <= 0;
			{ sr_last, sr_vlast } <= 2'b00;
		end

		assign	wide_sdata = { {(SRWIDTH-PW){1'b0}}, s_data };

		always @(posedge i_pixclk)
		if (pix_reset)
			sr_data <= 0;
		else if (pix_clearing)
			sr_data <= 0;
		else case({ (s_valid && s_ready), (sr_valid && !afifo_full) })
		2'b00: begin end
				// Verilator lint_off WIDTH
		2'b10: sr_data <= sr_data | (wide_sdata << (SRWIDTH-PW-sr_fill));
				// Verilator lint_on  WIDTH
		2'b01: sr_data <= sr_data << DW;
		2'b11: if (sr_last)
				sr_data <= wide_sdata << (SRWIDTH-PW);
			else
				// Verilator lint_off WIDTH
				sr_data <= (sr_data << DW)
					|(wide_sdata << (SRWIDTH+DW-PW-sr_fill));
				// Verilator lint_on  WIDTH
		endcase

		// Verilator lint_off WIDTH
		assign	s_ready = (sr_fill <= SRWIDTH) || !afifo_full;
		// Verilator lint_on  WIDTH
		// }}}
	end else begin : NO_PACKING
		assign	sr_valid =  s_valid;
		assign	s_ready  = !afifo_read;
		assign	sr_data  = s_data;
		assign	sr_last  = s_hlast;
		assign	sr_vlast = s_vlast;
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Push bus words into an asynchronous FIFO
	// {{{

	generate if (OPT_ASYNC_CLOCKS)
	begin : GEN_CLK_XROSSING
		reg	r_last_clr, r_pix_clearing;
		wire	pix_clr_ready;

		afifo #(
				.WIDTH(DW+2), .LGFIFO(3)
		) pxafifo (
			// {{{
			.i_wclk(i_pixclk), .i_wr_reset_n(!pix_reset),
			.i_wr(sr_valid),
				.i_wr_data({ sr_vlast, sr_last,
					sr_data[SRWIDTH-1:SRWIDTH-DW] }),
				.o_wr_full(afifo_full),
			.i_rclk(i_clk), .i_rd_reset_n(!i_reset),
			.i_rd(afifo_read),
			.o_rd_data({ afifo_vlast, afifo_hlast, afifo_data }),
			.o_rd_empty(afifo_empty)
			// }}}
		);

		tfrstb
		u_tfrstb (
			.i_a_clk(i_pixclk), .i_a_reset_n(!pix_reset),
			.i_a_valid(!i_pix_en && !r_last_clr),
			.o_a_ready(pix_clr_ready),

			.i_b_clk(i_clk), .i_b_reset_n(!i_reset),
			.o_b_valid(wb_clr),
			.i_b_ready(1'b1)
		);

		always @(posedge i_pixclk)
		if (pix_reset)
			r_last_clr <= 1'b1;
		else if (!i_pix_en)
			r_last_clr <= 1'b1;
		else if (r_last_clr)
			 r_last_clr <= !pix_clr_ready;

		always @(posedge i_pixclk)
		if (pix_reset)
			r_pix_clearing <= 1'b1;
		else if (!i_pix_en)
			r_pix_clearing <= 1'b1;
		else if (r_pix_clearing)
			 r_pix_clearing <= r_last_clr || !pix_clr_ready;

		assign	pix_clearing = r_pix_clearing || !i_pix_en;
	end else begin : NO_ASYNC_FIFO
		assign	afifo_full  =  sr_valid && !afifo_read;
		assign	afifo_empty = !sr_valid;
		assign	afifo_vlast = sr_vlast;
		assign	afifo_hlast = sr_last;
		assign	afifo_data = sr_data[SRWIDTH-1:SRWIDTH-DW];

		assign	wb_clr = !i_pix_en;
		assign	pix_clearing = !i_pix_en;
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Push bus words into a larger synchronous FIFO
	// {{{

	generate if (OPT_ONESHOT)
	begin : GEN_FIFO_FLUSH
		reg	r_flush;

		initial	r_flush = 1'b0;
		always @(posedge i_clk)
		if (i_reset || wb_clr)
			r_flush <= 1'b0;
		else if (afifo_empty && sfifo_empty)
			r_flush <= 1'b0;
		else if (afifo_read && !afifo_empty && afifo_hlast && afifo_vlast)
			r_flush <= 1'b1;

		assign	wb_flush = r_flush;
	end else begin : NO_FIFO_FLUSH
		assign	wb_flush = 1'b0;
	end endgenerate

	sfifo #(
		.BW(DW+2), .LGFLEN(LGFIFO), .OPT_ASYNC_READ(1'b0)
	) pxsfifo (
		.i_clk(i_clk), .i_reset(i_reset || wb_clr),
		.i_wr(afifo_read && !afifo_empty),
			.i_data({ afifo_vlast, afifo_hlast, afifo_data }),
			.o_full(sfifo_full), .o_fill(sfifo_fill),
		.i_rd(sfifo_read),
			.o_data({ sfifo_vlast, sfifo_hlast, sfifo_data }),
			.o_empty(sfifo_empty)
	);

	assign	afifo_read = !sfifo_full || sfifo_read;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Overflow checking
	// {{{

	// wb_syncd
	// {{{
	always @(posedge i_clk)
	if (i_reset || wb_clr)
		wb_syncd <= 1'b1;
	else if (sfifo_read && !sfifo_empty)
	begin
		if (sfifo_hlast && sfifo_vlast)
			wb_syncd <= 1'b1;
		else if (!i_wb_en)
			wb_syncd <= 1'b0;
	end
	// }}}

	// wb_ypos, wb_eof
	// {{{
	always @(posedge i_clk)
	if (i_reset || wb_clr || !i_wb_en || !wb_syncd)
	begin
		wb_ypos <= 0;
		wb_eof  <= 0;
	end else if (sfifo_read && !sfifo_empty && sfifo_hlast)
	begin
		wb_eof <= 1'b0;
		if (sfifo_vlast)
			wb_ypos <= 0;
		else if (wb_ypos < i_height)
			wb_ypos <= wb_ypos + 1;
		else
			wb_eof <= 1'b1;
	end
	// }}}

	// wb_word, wb_eol
	// {{{
	always @(posedge i_clk)
	if (i_reset || wb_clr || !i_wb_en || !wb_syncd)
	begin
		wb_word <= 0;
		wb_eol  <= 0;
	end else if (sfifo_read && !sfifo_empty)
	begin
		wb_eol <= 1'b0;
		if (wb_word < i_mem_words)
			wb_word <= wb_word + 1;
		else
			wb_eol <= 1'b1;
		if (sfifo_hlast)
			wb_word <= 0;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read synchronous FIFO into Wishbone
	// {{{
	generate if (AW > LGFRAME)
	begin : GEN_WIDE_NWORDS
		assign	wide_nwords = { {(AW-LGFRAME){1'b0}}, i_mem_words };
	end else begin : TRUNK_NWORDS
		assign	wide_nwords = i_mem_words[AW-1:0];
	end endgenerate

	// o_err
	// {{{
	// Errors -cannot- be cleared locally, lest the error accumulate in the
	// data.  Hence, o_err note the presence of an error until such time
	// as i_en goes low and hence wb_clr gets set.
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 0;
	else begin
		if (wb_clr || !i_wb_en)
			o_err <= 1'b0;
		if (sfifo_read && sfifo_hlast && sfifo_vlast)
			o_err <= 1'b0;
		if (o_wb_cyc && i_wb_err)
			o_err <= 1'b1;
		if (wb_eol || wb_eof)
			o_err <= 1'b1;
	end
	// }}}

	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc || i_wb_err || wb_clr || o_err)
		wb_outstanding <= 0;
	else case({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b00: begin end
	2'b10: wb_outstanding <= wb_outstanding + 1;
	2'b01: wb_outstanding <= wb_outstanding - 1;
	2'b11: begin end
	endcase

	always @(posedge i_clk)
	if (i_reset || !o_wb_cyc || i_wb_err || wb_clr || o_err)
		wb_zero <= 1;
	else case({ o_wb_stb && !i_wb_stall, i_wb_ack })
	2'b00: begin end
	2'b10: wb_zero <= 1'b0;
	2'b01: wb_zero <= (wb_outstanding <= 1);
	2'b11: begin end
	endcase

	always @(posedge i_clk)
	if (i_reset || wb_clr || o_err || (o_wb_cyc && i_wb_err)
						|| !i_wb_en || !wb_syncd)
	begin
		o_wb_cyc <= 0;
		o_wb_stb <= 0;
	end else if (o_wb_cyc)
	begin
		if (!i_wb_stall)
		begin
			o_wb_stb <= o_wb_stb && !sfifo_empty && !wb_done;
			if (o_wb_addr >= line_addr + wide_nwords)
				o_wb_stb <= 0;
		end

		if (!o_wb_stb && wb_zero)
			o_wb_cyc <= 0;
	end else if (!wb_done && ((wb_flush && !sfifo_empty)
					|| (|sfifo_fill[LGFIFO:LGFIFO-1])))
		{ o_wb_cyc, o_wb_stb } <= 2'b11;

	always @(posedge i_clk)
	if (i_reset)
	begin
		o_wb_addr <= 0;
		line_addr <= 0;
		wb_hlast <= 1'b0;
		wb_vlast <= 1'b0;
	end else if (wb_clr || o_err || !i_wb_en || !wb_syncd || o_done)
	begin
		o_wb_addr <= i_baseaddr;
		line_addr <= i_baseaddr;
		wb_hlast <= 1'b0;
		wb_vlast <= 1'b0;
	end else if (!o_wb_stb || !i_wb_stall)
	begin
		wb_hlast <= !sfifo_empty && sfifo_hlast;
		wb_vlast <= !sfifo_empty && sfifo_vlast;

		if (o_wb_stb && wb_hlast && wb_vlast)
		begin
			o_wb_addr <= i_baseaddr;
			line_addr <= i_baseaddr;
		end else if (o_wb_stb && wb_hlast)
		begin
			o_wb_addr <= line_addr + wide_nwords;
			line_addr <= line_addr + wide_nwords;
		end else if (o_wb_stb)
			o_wb_addr <= o_wb_addr + 1;
	end

	// o_done*
	// {{{
	generate if (OPT_ONESHOT)
	begin : GEN_DONE
		reg	r_done;

		initial	r_done = 1'b0;
		always @(posedge i_clk)
		if (i_reset || !OPT_ONESHOT)
			r_done <= 1'b0;
		else if (wb_clr || o_err || !i_wb_en || !wb_syncd)
			r_done <= 1'b0;
		else if (!o_wb_stb || !i_wb_stall)
			r_done <= !sfifo_empty && sfifo_hlast && sfifo_vlast;

		assign	wb_done = r_done;
		assign	o_done = wb_done && !o_wb_cyc;
	end else begin : NEVER_DONE
		assign	{ o_done, wb_done } = 2'b00;
	end endgenerate
	// }}}


	always @(posedge i_clk)
	if (OPT_LOWPOWER && (i_reset || wb_clr || o_err || !i_wb_en || !wb_syncd))
		o_wb_data <= 0;
	else if ((!o_wb_stb || !i_wb_stall) && (!OPT_LOWPOWER || !sfifo_empty))
		o_wb_data <= sfifo_data;

	assign	sfifo_read = o_err || wb_eol || wb_eof
			|| ((!o_wb_cyc && |sfifo_fill[LGFIFO:LGFIFO-1])
			|| (o_wb_stb && !i_wb_stall));

	assign	o_wb_we = 1'b1;
	assign	o_wb_sel = {(DW/8){1'b1}};
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;

	assign	unused = &{ 1'b0, i_wb_data, sfifo_fill[LGFIFO-2:0] };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
