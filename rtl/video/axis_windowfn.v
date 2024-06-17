////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/axis_windowfn.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Create a wrapper around the windowfn.v module in order to give
//		it an AXI stream interface.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
module	axis_windowfn #(
		// {{{
		parameter	IW = 16, OW=16, TW=16, LGNFFT = 4,
		parameter [0:0]	OPT_FIXED_TAPS = 1'b0,
		parameter [0:0]	OPT_HIRES      = 1'b0,
		parameter	INITIAL_COEFFS = ""
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset_n,
		//
		input	wire			i_tap_wr,
		input	wire	[TW-1:0]	i_tap,
		//
		input	wire			i_tvalid,
		output	wire			o_tready,
		input	wire	[IW-1:0]	i_tdata,
		// NO TLAST on the input
		//
		output	wire			o_tvalid,
		input	wire			i_tready,
		output	wire	[OW-1:0]	o_tdata,
		output	wire			o_tlast
		// }}}
	);

	// Local declarations
	// {{{
	localparam		LGFLEN = 4;
	wire	i_reset;

	wire			skd_valid, skd_ready;
	wire	[IW-1:0]	skd_data;

	reg	[LGNFFT:0]	initial_count;
	wire			initial_frame;

	reg			r_ce, r_alt_ce;
	reg	[IW-1:0]	r_sample;

	wire			wndw_ce, wndw_frame;
	wire	[OW-1:0]	wndw_sample;

	wire	[LGFLEN:0]	of_fill;
	wire			of_full, of_empty;

	reg	[LGFLEN:0]	fifo_fill;
	reg			fifo_full;

	assign	i_reset = !i_reset_n;
	// }}}

	skidbuffer #(
		// {{{
		.DW(IW),
		.OPT_OUTREG(0)
		// }}}
	) iskid (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(i_tvalid), .o_ready(o_tready), .i_data(i_tdata),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data(skd_data)
		// }}}
	);

	initial	initial_count = 0;
	always @(posedge i_clk)
	if (i_reset)
		initial_count <= 0;
	else if (skd_valid && skd_ready && !initial_count[LGNFFT])
		initial_count <= initial_count + 1;

	assign	initial_frame = !initial_count[LGNFFT];
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(initial_count <= (1<<LGNFFT));
`endif

	// r_sample
	// {{{
	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		r_sample <= skd_data;
	// }}}

	// (r_ce || r_alt_ce), d_ce, p_ce, o_ce
	generate if (OPT_HIRES)
	begin : GEN_HIRES_OPTION
		reg	[2:0]	ce_phase;

		assign	skd_ready = (ce_phase == 0) && !fifo_full;

		// ce_phase
		// {{{
		initial	ce_phase = 0;
		always @(posedge i_clk)
		if (i_reset)
			ce_phase <= 0;
		else if (skd_valid && skd_ready)
			ce_phase <= 5;
		else if (ce_phase > 0)
			ce_phase <= ce_phase - 1;
		// }}}

		// r_ce
		// {{{
		initial	r_ce = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_ce <= 0;
		else if (skd_valid && skd_ready)
			r_ce <= 1;
		else
			r_ce <= 0;
		// }}}

		// r_alt_ce
		// {{{
		initial	r_alt_ce = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_alt_ce <= 0;
		else if (ce_phase == 3)
			r_alt_ce <= 1;
		else
			r_alt_ce <= 0;
		// }}}

		hires #(
			// {{{
			.IW(IW), .OW(OW), .TW(TW), .LGNFFT(LGNFFT),
			.OPT_FIXED_TAPS(OPT_FIXED_TAPS),
			.INITIAL_COEFFS(INITIAL_COEFFS), .OPT_TLAST_FRAME(1'b1)
			// }}}
		) u_hires (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_tap_wr(i_tap_wr), .i_tap(i_tap),
			//
			.i_ce(r_ce), .i_sample(r_sample), .i_alt_ce(r_alt_ce),
			//
			.o_frame(wndw_frame), .o_ce(wndw_ce), .o_sample(wndw_sample)
			// }}}
		);

	end else begin : GEN_TRADITIONAL
		assign	skd_ready = !r_ce && !fifo_full;

		// r_ce
		// {{{
		initial	r_ce = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_ce <= 0;
		else if (skd_valid && skd_ready)
			r_ce <= 1;
		else
			r_ce <= 0;
		// }}}

		// r_alt_ce
		// {{{
		initial	r_alt_ce = 0;
		always @(posedge i_clk)
		if (i_reset)
			r_alt_ce <= 0;
		else if (r_ce)
			r_alt_ce <= 1;
		else
			r_alt_ce <= 0;
		// }}}

		windowfn #(
			// {{{
			.IW(IW), .OW(OW), .TW(TW), .LGNFFT(LGNFFT),
			.OPT_FIXED_TAPS(OPT_FIXED_TAPS),
			.INITIAL_COEFFS(INITIAL_COEFFS),
			.OPT_TLAST_FRAME(1'b1)
			// }}}
		) u_window (
			// {{{
			.i_clk(i_clk), .i_reset(i_reset),
			.i_tap_wr(i_tap_wr), .i_tap(i_tap),
			//
			.i_ce(r_ce), .i_sample(r_sample), .i_alt_ce(r_alt_ce),
			//
			.o_frame(wndw_frame), .o_ce(wndw_ce), .o_sample(wndw_sample)
			// }}}
		);

	end endgenerate

	sfifo #(
		// {{{
		.BW(OW+1), .LGFLEN(LGFLEN), .OPT_ASYNC_READ(1'b0)
		// }}}
	) ofifo (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wr(wndw_ce), .i_data({ wndw_frame, wndw_sample }),
		.o_full(of_full), .o_fill(of_fill),
		.i_rd(o_tvalid && i_tready), .o_data({ o_tlast, o_tdata }),
		.o_empty(of_empty)
		// }}}
	);

	assign	o_tvalid = !of_empty;

	// fifo_fill - End to end FIFO fill measure
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		fifo_fill <= 0;
	else case({ (skd_valid && skd_ready && !initial_frame), (o_tvalid && i_tready) })
	2'b10: fifo_fill <= fifo_fill + 2;
	2'b01: fifo_fill <= fifo_fill - 1;
	2'b11: fifo_fill <= fifo_fill + 1;
	default: begin end
	endcase
	// }}}

	// fifo_full
	// {{{
	// Used to guarantee the window pipeline doesn't fill the result FIFO
	always @(posedge i_clk)
	if (i_reset)
		fifo_full <= 0;
	else case({ (skd_valid && skd_ready && !initial_frame), (o_tvalid && i_tready) })
	2'b10: fifo_full <= ((fifo_fill + 3) >= (1<<LGFLEN));
	2'b01: fifo_full <= ((fifo_fill    ) >= (1<<LGFLEN));
	2'b11: fifo_full <= ((fifo_fill + 2) >= (1<<LGFLEN));
	default: begin end
	endcase
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, of_fill, of_full, of_empty };
	// Verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg			f_past_valid;
	reg	[2:0]		f_past_count;
	reg			r_initial;
	wire			d_ce, p_ce, first_block;
	reg	[LGFLEN:0]	f_fill, dwidx, f_initial;


	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	initial	f_past_count = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		f_past_count <= 0;
	else if (!f_past_count[2])
		f_past_count <= f_past_count+1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!i_tvalid);
	end else if ($past(i_tvalid && !o_tready))
	begin
		assume(i_tvalid);
		assume($stable(i_tdata));
	end

	always @(*)
	if (!i_reset)
	begin
		assert(fifo_full == ((fifo_fill + 1) >= (1<<LGFLEN)));
		assert(fifo_fill <= (1<<LGFLEN));
		if (of_full)
			assert(!wndw_ce);

		if (!f_past_count[2])
		begin
			assert(initial_frame);
			assert(initial_count <= f_past_count);
		end else
			assert(f_past_count[1:0] == 2'b00);
	end

	always @(posedge i_clk)
	if (i_reset)
		r_initial <= 1;
	else if (skd_valid && skd_ready)
		r_initial <= initial_frame;

	wire	[LGNFFT-1:0]	tapwidx;
	wire	[LGNFFT:0]	f_phase;

	assign	d_ce = u_window.d_ce;
	assign	p_ce = u_window.p_ce;
	assign	first_block = u_window.first_block;
	assign	dwidx = u_window.dwidx;
	assign	tapwidx = u_window.tapwidx;
	assign	f_initial = initial_count - (r_ce ? 1:0);
	assign	f_phase = u_window.f_phase;

	always @(posedge i_clk)
	if (!i_reset && !r_ce && !r_alt_ce)
		assert(!f_phase[0]);

	always @(posedge i_clk)
	if (!i_reset && f_past_count[2])
	begin
		assert(d_ce == $past(!r_initial&&(r_ce || r_alt_ce)  ));
		assert(p_ce == $past(!r_initial&&(r_ce || r_alt_ce),2));
		if (initial_frame || (r_initial && r_ce))
			assert(first_block);
		if (r_ce)
			assert(initial_count >= 1);
		if (initial_frame)
			assert(dwidx == f_initial[LGNFFT-1:0]);
		else if (!r_initial)
			assert(!first_block);
		else // if (r_initial && !initial_frame)
			assert(r_ce || r_alt_ce || !first_block);
	end

	always @(*)
	begin
		f_fill = of_fill;

		if (!r_initial && r_ce)
			f_fill = f_fill + 2;
		if (!r_initial && r_alt_ce)
			f_fill = f_fill + 1;
		if (d_ce)
			f_fill = f_fill + 1;
		if (p_ce)
			f_fill = f_fill + 1;
		if (wndw_ce)
			f_fill = f_fill + 1;
	end

	always @(posedge i_clk)
	if (!i_reset && f_past_count[2])
	begin
		assert(fifo_fill == f_fill);
	end


	always @(*)
	if (!i_reset)
	begin
		if (first_block)
			assert(r_initial);
		else if (!r_ce && !r_alt_ce && r_initial)
			assert(f_phase == 0);
	end

	always @(*)
	if (!i_reset && first_block)
		assert(of_fill == 0);

	always @(*)
	if (r_initial && !initial_frame && first_block)
		assert(&f_phase[LGNFFT:1]);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[1:0]	cvr_frames;
	always @(posedge i_clk)
	if (i_reset)
		cvr_frames <= 0;
	else if (o_tvalid && i_tready && o_tlast && !cvr_frames[1])
		cvr_frames <= cvr_frames + 1;

	always @(posedge i_clk)
	if (!i_reset)
	begin
		cover(cvr_frames[0]);
		cover(cvr_frames[1]);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Assume we *never* write to the coefficients
	//   This is an assumption of the Window Function submodule proof
	always @(*)
		assume(!i_tap_wr);

	// If we never write to the underlying coefficients, then ... the
	// tap write index should always be zero.  This should probably be
	// asserted within windowfn and now here, but this is where I'm working
	// today, so I'll put it here.
	always @(*)
	if (!i_reset)
		assert(tapwidx == 0);

//	always @(posedge i_clk)
//	if (f_past_count[2])
//		assume(i_tvalid || $past(i_tvalid) || $past(i_tvalid, 2)
//			|| $past(i_tvalid, 3));

	// }}}
`endif
// }}}
endmodule
