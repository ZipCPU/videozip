////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/axis_fft.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	An AXI-stream wrapper for the FFT
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
`default_nettype none
// }}}
module axis_fft #(
		// {{{
		parameter	[0:0]	OPT_IGNORE_TLAST = 1'b0,
		parameter	LGWIDTH = 11,
		parameter	IW=15, OW=21,
		parameter	NCK = 2
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset_n,
		// Incoming data interface
		input	wire			i_tvalid,
		output	wire			o_tready,
		input	wire	[2*IW-1:0]	i_tdata,
		input	wire			i_tlast,
		// Outgoing data interface
		output	wire			o_tvalid,
		input	wire			i_tready,
		output	wire	[2*OW-1:0]	o_tdata,
		output	wire			o_tlast
		// }}}
	);

	// Local declarations
	// {{{
	wire			pause;
	reg			w_iready;
	wire			m_ivalid, i_reset;
	wire			w_ilast;
	reg	[LGWIDTH-1:0]	in_counter, out_counter;
	reg			out_ce;
	reg			skid_valid, r_otlast, syncd;
	wire			skid_ready;
	//
	// FFT inputs
	reg			r_ce;
	wire	[2*IW-1:0]	fft_input;
	wire	[2*OW-1:0]	fft_output;
	wire			fft_first;
	//

	assign	i_reset = !i_reset_n;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pause for NCK clocks between samples
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (NCK == 0)
	begin : NO_INPUT_DELAYS_REQUIRED

		assign	pause = 0;

	end else begin : NCK_PAUSE
		reg				r_pause;
		reg	[$clog2(NCK+1)-1:0]	pause_counter;

		initial	pause_counter = 0;
		initial	r_pause = 0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			pause_counter <= 0;
			r_pause <= 0;
		end else if (r_ce)
		begin
			pause_counter <= NCK[$clog2(NCK+1)-1:0];
			r_pause <= (NCK > 0);
		end else if (pause_counter > 0)
		begin
			pause_counter <= pause_counter - 1;
			r_pause <= (pause_counter > 1);
		end

		assign	pause = r_pause;
`ifdef	FORMAL
		always @(*)
			assert(pause_counter <= NCK);
		always @(*)
			assert(pause == (pause_counter != 0));
`endif
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
		// {{{
		.OPT_LOWPOWER(0), .OPT_OUTREG(0), .DW(2*IW+1)
		// }}}
	) ibuf(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(i_tvalid), .o_ready(o_tready),
			.i_data({ i_tdata, i_tlast }),
		.o_valid(m_ivalid), .i_ready(w_iready),
			.o_data({ fft_input, w_ilast })
		// }}}
	);

	// w_iready -- combinatorial skid buffer input, when ready for nxt smpl
	// {{{
	always @(*)
	begin
		w_iready = 1;
		if (pause)
			w_iready = 0;
		if (skid_valid && !skid_ready)
			w_iready = 0;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Track the incoming i_tlast values and lock to frames (if so config'd)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// in_counter -- count where we are within the incoming frame
	// {{{
	// This is an important part of synchronizing with the incoming TLAST
	// if so required.  It's pointless otherwise.
	initial	in_counter = 0;
	always @(posedge i_clk)
	if (!i_reset_n || OPT_IGNORE_TLAST)
		in_counter <= 0;
	else if (m_ivalid && w_iready)
	begin
		// if i_tlast && !&in_counter, then we've got a bug
		// Best chance is to ride it out here, while waiting
		// for tlast using i_ce
		in_counter <= in_counter + 1;
	end
	// }}}

	// r_ce
	// {{{
	// r_ce drives the logic of the entire design.  All FFT logic is clocked
	// based upon it.
	//
	// WARNING: r_ce has a *HIGH* fanout.
	always @(*)
	begin
		r_ce = (m_ivalid & w_iready);
		if (!OPT_IGNORE_TLAST)
		begin
			// If we are paying attention to TLAST and the input
			// doesn't place TLAST in the right place, then we'll
			// wait here until TLAST is available to us.
			if ((&in_counter) != w_ilast)
				r_ce = 0;
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The FFT itself
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

`ifndef	FORMAL
	fftmain thefft(i_clk, !i_reset_n, r_ce, fft_input, fft_output,
			fft_first);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Run the FFT output through a skidbuffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// syncd -- wait for the first FFT result
	// {{{
	initial	syncd = 0;
	always @(posedge i_clk)
	if (!i_reset_n)
		syncd <= 0;
	else if (r_ce && fft_first)
		syncd <= 1;
	// }}}

	// out_counter -- need this to know when to set TLAST
	// {{{
	initial out_counter = 0;
	always @(posedge i_clk)
	if (!i_reset_n)
		out_counter <= 0;
	else if (r_ce && fft_first)
		out_counter <= 1;
	else if (r_ce && syncd)
		out_counter <= out_counter + 1;
`ifdef	FORMAL
	always @(*)
	if (!syncd)
		assert(out_counter == 0);
`endif
	// }}}

	// out_ce
	// {{{
	initial	out_ce = 0;
	always @(posedge i_clk)
	if (i_reset)
		out_ce <= 0;
	else if (r_ce)
		out_ce <= 1;
	else if (skid_ready)
		out_ce <= 0;
	// }}}

	// r_otlast -- TLAST going into the skid buffer
	// {{{
	initial	r_otlast = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_otlast <= 0;
	else if (r_ce && syncd && (&out_counter[LGWIDTH-1:1]) && !out_counter[0])
		r_otlast <= 1;
	else if (skid_ready)
		r_otlast <= 0;
	// }}}

	// skid_valid -- valid data going into the skid buffer
	always @(*)
		skid_valid = (fft_first || syncd) & out_ce;

	skidbuffer #(
		// {{{
		.OPT_LOWPOWER(0), .OPT_OUTREG(1), .DW(2*OW+1)
		// }}}
	) obuf(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(skid_valid), .o_ready(skid_ready),
			.i_data({ fft_output, r_otlast }),
		.o_valid(o_tvalid), .i_ready(i_tready),
			.o_data({ o_tdata, o_tlast })
		// }}}
	);
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	// Declarations
	// {{{
	(* anyseq *)	reg	f_first;
	(* anyseq *)	reg	f_outputs;
	reg			f_started_input;
	reg	[LGWIDTH-1:0]	f_fft_ocounter;
	reg			f_past_valid;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Basic setup
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(*)
	begin
		assume(f_first   == fft_first);
		assume(f_outputs == fft_output);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Faux FFT assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// f_started_input
	// {{{
	// Used to guarantee fft_first stays low until at least some data has
	// been given to the FFT.
	initial	f_started_input = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_started_input <= 0;
	else if (r_ce)
		f_started_input <= 1;
	// }}}

	// f_fft_ocounter
	// {{{
	// Used for setting fft_first properly
	always @(posedge i_clk)
	if (i_reset)
		f_fft_ocounter <= 0;
	else if (r_ce && (syncd || fft_first))
		f_fft_ocounter <= f_fft_ocounter + 1;
	else if (!syncd)
		f_fft_ocounter <= 0;
	// }}}

	always @(*)
	if (!f_started_input)
		assume(!fft_first);

	// FFT outputs only change following r_ce
	// {{{
	always @(posedge i_clk)
	if (f_past_valid && (!$past(r_ce) && !$past(i_reset)))
	begin
		assume($stable(fft_output));
		assume($stable(fft_first));
	end
	// }}}

	// fft_first will only be true on the first of any FFT frame
	// {{{
	// Except ... we can't constrain it until we've had our first output.
	// Therefore, only constrain fft_first if syncd is true.
	always @(*)
	if (f_fft_ocounter != 0)
		assume(!fft_first);
	else if (syncd)
		assume(fft_first == (f_fft_ocounter == 0));
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Design assertions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!(&out_counter))
		assert(!r_otlast);
	else if (skid_valid)
		assert(r_otlast == (&out_counter));
	else
		assert(!r_otlast);

	always @(*)
	if (!i_reset && syncd)
		assert(f_fft_ocounter == out_counter);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming AXI-stream properties--required by the skidbuffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_tvalid);
	else if ($past(i_tvalid && !o_tready))
	begin
		assume(i_tvalid);
		assume($stable(i_tdata));
		assume($stable(i_tlast));
	end
	// }}}
`endif
// }}}
endmodule
