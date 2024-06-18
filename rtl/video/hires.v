////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/hires.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Implements a polyphase FFT window.  There's no special timing
//		magic here, and no pipelining: the FFT can arrive no faster
//	than one sample every 2*(1<<LGFLEN) cycles.  Hence, for a filter of NM
//	(as I like to call it), or 2*(1<<LGNFFT)*(1<<LGFLEN) coefficients, N
//	samples are allowed to arrive in 2NM cycles.
//
//	i_ce:		One new sample arrives on every cycle where i_ce
//			is true.
//
//	i_alt_ce:	Should be set halfway between i_ce cycles.
//
//			One output will be generated for every clock cycle
//			where (i_ce || i_alt_ce) is true.
//
// Creator:     Dan Gisselquist, Ph.D.
//              Gisselquist Tecnology, LLC
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
module	hires #(
		// {{{
		parameter		IW=16, // Input bit-width
					OW=16,	// Output bit-width
					TW=16,	// Coefficient bit-width
					LGNFFT = 8,	// log_2(FFT size)
					LGFLEN = 3,	// log_2(filter len)
		// parameter		LGSTEPSZ = LGNFFT-1,
		parameter	[0:0]	OPT_FIXED_TAPS  = 1'b0,
		parameter	[0:0]	OPT_TLAST_FRAME = 1'b0,
		parameter		INITIAL_COEFFS = "",
	//
		localparam		AW=IW+TW+LGFLEN,
		localparam		LGMEMSZ=LGNFFT+LGFLEN,
		localparam		M = (1<<(LGFLEN))
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_tap_wr,
		input	wire	[(TW-1):0]	i_tap,
		//
		input	wire			i_ce,	// New data marker
		input	wire	[(IW-1):0]	i_sample,
		input	wire			i_alt_ce,
		//
		output	reg			o_frame, o_ce,
		output	reg	[(OW-1):0]	o_sample
		// }}}
	);

	// Register/signal declarations
	// {{{

	// Coefficient and sample data memory
	reg	[(TW-1):0]	cmem	[0:(1<<LGMEMSZ)-1];
	reg	[(IW-1):0]	dmem	[0:(1<<LGMEMSZ)-1];

	reg		[LGMEMSZ-1:0]	dwidx, didx, tidx, lidx;
	reg				top_of_block;
	reg				p_ce, d_ce, m_ce;
	reg	signed	[IW+TW-1:0]	product;
	reg	signed	[IW-1:0]	data;
	reg	signed	[TW-1:0]	tap;
	reg		[LGFLEN-1:0]	acc_ce_counter;
	reg				accumulate = 1'b0;
	reg	signed	[AW-1:0]	acc;
	reg				pre_frame;
	wire		[LGMEMSZ-1:0]	tapwidx;
	integer				iw;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Load the coefficients
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Initialize the coefficient memory--from a file if necessary
	// {{{
	initial begin
		//
		// Clear all coefficients to zero, lest the readmemh leave
		// some undefined
		//
		for(iw=0; iw < (1<<LGMEMSZ); iw=iw+1)
			cmem[iw] = 0;
		if (OPT_FIXED_TAPS || INITIAL_COEFFS != 0)
			$readmemh(INITIAL_COEFFS, cmem);
	end
	// }}}

	generate if (OPT_FIXED_TAPS)
	begin : SET_FIXED_TAPS
		// Fixed coefficients do not change
		// {{{

		// Don't need to use any of the coefficient writing logic
		// here, so let's mark it all as unused

		assign	tapwidx = 0;
		// Make Verilators -Wall happy
		// Verilator lint_off UNUSED
		wire	ignored_inputs;
		assign	ignored_inputs = &{ 1'b0, tapwidx, i_tap_wr, i_tap };
		// Verilator lint_on  UNUSED
		// }}}
	end else begin : DYNAMICALLY_SET_TAPS
		// Allow the user to dynamically load the coefficient set
		// {{{
		// Coef memory write index
		reg	[(LGMEMSZ-1):0]	r_tapwidx;

		initial	r_tapwidx = 0;
		always @(posedge i_clk)
		if(i_reset)
			r_tapwidx <= 0;
		else if (i_tap_wr)
			r_tapwidx <= r_tapwidx + 1'b1;

		always @(posedge i_clk)
		if (i_tap_wr)
			cmem[r_tapwidx] <= i_tap;

		assign	tapwidx = r_tapwidx;
		// }}}
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Record the incoming data into a local memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Notice how this data writing section is *independent* of the reset,
	// depending only upon new sample data.

	initial	dwidx = 0;
	always @(posedge i_clk)
	if (i_ce)
		dwidx <= dwidx + 1'b1;

	always @(posedge i_clk)
	if (i_ce)
		dmem[dwidx] <= i_sample;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Index generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// top_of_block
	// {{{
	// Keep track of the top of the block.  The top of the block is the
	// first incoming data sample on an FFT or half FFT boundary.  This
	// is where data processing starts from.
	//
	localparam	[LGNFFT-1:0]	M_2 = -2;
	initial	top_of_block = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		top_of_block <= 1'b1;
	else if (i_alt_ce)
		// top_of_block <= (&tidx[LGMEMSZ-1:LGNFLEN])&&(tidx[LGMEMSZ;
		top_of_block <= (tidx[LGNFFT-1:0] == M_2);
	else if (i_ce)
		top_of_block <= 1'b0;
	// }}}

	// didx, tidx, lidx
	// {{{
	// Data and coefficient memory indices.
	//
	// Need to be careful how this is done:
	// 1. Need to read the oldest memory first.  This is the memory that
	//    would be rewritten during our operation.
	// 2. The additions below skip by FFT lengths.
	//
	initial	begin
		didx = 0;
		tidx = -1;
	end
	always @(posedge i_clk)
	if (i_reset)
	begin
		didx <= 0;
		tidx <= -1;
		lidx <= 0;
	end else if (i_ce && top_of_block)
	begin
		didx <= dwidx + 1'b1;
		lidx <= dwidx + 1'b1;
		tidx <= 0;
	end else if (i_ce || i_alt_ce)
	begin
		// Process the next point in this FFT
		// didx[LGMEMSZ-1:LGNFFT] <= didx[LGMEMSZ-1:LGNFFT] + 1'b1;
		// didx[LGNFFT-1:0] <= didx[LGNFFT-1:0] + 1'b1;
		didx <= lidx + 1'b1;
		lidx <= lidx + 1'b1;
		tidx[LGMEMSZ-1:LGNFFT] <= 0;
		tidx[LGNFFT-1:0] <= tidx[LGNFFT-1:0] + 1'b1;
	end else if (!(&tidx[LGMEMSZ-1:LGNFFT]))
	begin
		// Process the next point in this FFT
		didx[LGMEMSZ-1:LGNFFT] <= didx[LGMEMSZ-1:LGNFFT] + 1'b1;
		tidx[LGMEMSZ-1:LGNFFT] <= tidx[LGMEMSZ-1:LGNFFT] + 1'b1;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// New frame marker
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	pre_frame = 0;
	always @(posedge i_clk)
	if (i_reset)
		pre_frame <= 0;
	else if ((i_ce)&&(top_of_block))
	begin
		pre_frame <= 1'b1;
	end else if ((o_ce)&&(o_frame))
		pre_frame <= 1'b0;

	initial	o_frame = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_frame <= 1'b0;
	else if (OPT_TLAST_FRAME)
		o_frame <= (d_ce)&&(pre_frame);
	else
		o_frame <= (p_ce)&&(pre_frame);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal frame/CE tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Following any initial i_ce, ...
	// 	m_ce: The memory will be valid
	// 	d_ce: The data (and coefficient), read from memory,will be valid
	// 	p_ce: The produc of data and coefficient is valid
	//
	initial	{ p_ce, d_ce, m_ce } = 3'h0;
	always @(posedge i_clk)
	if (i_reset)
		{ p_ce, d_ce, m_ce } <= 3'h0;
	else if ((i_ce)||(i_alt_ce))
		{ p_ce, d_ce, m_ce } <= 3'h1;
	else
		{ p_ce, d_ce, m_ce } <= { d_ce, m_ce, 1'b0 };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Read the data sample point, and the filter coefficient, from block
	// RAM.  Because this is block RAM, we have to be careful not to
	// do anything else here.
	initial	data = 0;
	initial	tap = 0;
	always @(posedge i_clk)
	begin
		data <= dmem[didx];
		tap  <= cmem[tidx];
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Product
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	// Multiply the two values together
	initial	product = 0;
`ifdef	FORMAL
	// Formal verification alternative
	// {{{
	wire	[IW+TW-1:0]	w_product;

	absmpy #(IW,TW) fmpy (data,tap, w_product);

	always @(posedge i_clk)
		product <= w_product;
	// }}}
`else
	always @(posedge i_clk)
		product <= data * tap;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Accumulator
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Decide if we need to add to the last value, or start over
	initial	accumulate = 0;
	initial	acc_ce_counter = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		acc_ce_counter <= 0;
		accumulate <= 1'b0;
	end else if (p_ce)
	begin
		acc_ce_counter <= M-2;
		accumulate <= 1'b1;
	end else if (acc_ce_counter > 0)
	begin
		acc_ce_counter <= acc_ce_counter - 1'b1;
		accumulate <= 1'b1;
	end else
		accumulate <= 1'b0;

	//
	// Our accumulator, summing 8-such values together
	//
	initial	acc = 0;
	always @(posedge i_clk)
	if (i_reset)
		acc <= 0;
	else if (p_ce)
		acc <= { {(AW-TW-IW){product[TW+IW-1]}}, product };
	else if (accumulate)
		acc <= acc + { {(AW-TW-IW){product[TW+IW-1]}}, product };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output stage
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Output CE
	//
	initial	o_ce = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_ce <= 0;
	else
		o_ce <= p_ce;

	//
	// Round to an output value
	// {{{
	generate if (OW == AW)
	begin : BIT_ADJUSTMENT_NONE

		initial	o_sample = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_sample <= 0;
		else if (p_ce)
			o_sample <= acc;

	end else if (OW < AW)
	begin : BIT_ADJUSTMENT_ROUNDING
		wire	[AW-1:0]	rounded;

		assign	rounded = acc + { {(OW){1'b0}}, acc[AW-OW],
				{(AW-OW-1){!acc[AW-OW]}} };

		initial	o_sample = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_sample <= 0;
		else if (p_ce)
			o_sample <= rounded[(AW-1):(AW-OW)];

		// verilator lint_off UNUSED
		wire	[AW-OW-1:0]	unused_bits;
		assign	unused_bits = rounded[AW-OW-1:0];
		// verilator lint_on  UNUSED
	end else // if (OW > AW)
	begin : BIT_ADJUSTMENT_EXTENDING

		always @(posedge i_clk)
		if (i_reset)
			o_sample <= 0;
		else if (p_ce)
			o_sample <= { acc, {(OW-AW){1'b0}} };

	end endgenerate
	// }}}

	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal verification / property section
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	(* anyconst *)	reg	f_dynamic_coeffs;

	// Keep track of the phase of this operation
	localparam	LSBPHASE = $clog2(M+4);//(LGFLEN<3) ? 3 : LGFLEN+1;
	reg	[LGMEMSZ+LSBPHASE-1:0]	f_phase;
	reg	[LGMEMSZ-1:0]		f_passed_idx, f_passw_idx,
					f_passed_diff;


	// f_phase
	// {{{
	// f_phase is used to track our current place in the algorithm.  We'll
	// use it to make assertions against.
	initial	f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE] = -1;
	initial	f_phase[LSBPHASE-1:0] = M;
	always @(posedge i_clk)
	if (i_reset)
	begin
		f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE] <= -1;
		f_phase[LSBPHASE-1:0] <= M;
	end else if (i_ce && top_of_block)
		f_phase <= 0;
	else if (i_ce || i_alt_ce)
	begin
		f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE]
			<= f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE] + 1;
		f_phase[LSBPHASE-1:0] <= 0;
	end else if (f_phase[LSBPHASE-1:0] < M+2)
		f_phase <= f_phase + 1;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about the inputs
	// {{{
	//
	always @(*)
	if (!(&f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE])
			|| (f_phase[LSBPHASE-1:0] != M))
		assume(tapwidx == 0);

	always @(*)
	if (!f_dynamic_coeffs && !OPT_FIXED_TAPS)
	begin
		assume(!i_tap_wr);
		assert(tapwidx == 0);
	end

	always @(*)
	if (tapwidx != 0)
	begin
		assume(!i_ce);
		assume(!i_alt_ce);
	end

	////////////////

	always @(*)
	if (!i_reset)
		assume(!i_ce || !i_alt_ce);

	always @(*)
	if (f_phase[LSBPHASE-1:0] < M-1)
		assume(!i_ce && !i_alt_ce);
	else if (!f_phase[LSBPHASE])
		assume(!i_ce);
	else // if (f_phase[LSBPHASE])
		assume(!i_alt_ce);

	always @(*)
	if (i_tap_wr)
		assume(!i_ce && !i_alt_ce);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our outputs
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_frame
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_frame);

	always @(*)
	if (o_frame)
	begin
		assert(o_ce && pre_frame);
		assert(f_phase[LSBPHASE +: LGMEMSZ] == 0);
	end
	always @(*)
	if (f_phase > 3)
		assert(!pre_frame);
	// }}}

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
		assert(o_ce || $stable(o_sample));

	// *_ce
	// {{{
	always @(*)
		assert(m_ce == (f_phase[LSBPHASE-1:0] == 0));
	always @(*)
		assert(d_ce == (f_phase[LSBPHASE-1:0] == 1));
	always @(*)
		assert(p_ce == (f_phase[LSBPHASE-1:0] == 2));
	always @(*)
		assert(o_ce == (f_phase[LSBPHASE-1:0] == 3));
	// }}}

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset && p_ce))
		assert(accumulate);

	always @(posedge i_clk)
	if (f_phase[LSBPHASE-1:0] == 2)
		assert(!accumulate);
	else if (!top_of_block && (f_phase[LSBPHASE-1:0] > 2)
			&& (f_phase[LSBPHASE-1:0] < M+1))
		assert(accumulate);
	else if (f_phase[LSBPHASE-1:0] >= M+2)
		assert(!accumulate);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(f_phase[LSBPHASE-1:0] == M+2)))
		assert($stable(acc));

	always @(*)
	if (!top_of_block)
	begin
		assert(tidx[LGNFFT-1:0]==f_phase[LGNFFT+LSBPHASE-1:LSBPHASE]);
		if (f_phase[LSBPHASE-1:0] < M)
			assert(tidx[LGNFFT +: LGFLEN] == f_phase[0 +: LGFLEN]);
		assert(f_phase[LSBPHASE-1:0] <= M+2);
	end else begin
		assert(&tidx[LGNFFT-1:0]);
		assert(&f_phase[LGNFFT+LSBPHASE-1:LSBPHASE]);
	end

	always @(*)
	if (top_of_block)
		assert(!i_alt_ce);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(top_of_block);
	else if ($past(i_ce))
		assert(!top_of_block);
	else if ($past(top_of_block))
		assert(top_of_block);

	// Tie lidx, didx and tidx together
	assign	f_passed_idx = didx-lidx;

	always @(*)
	if (!top_of_block)
		assert(f_passed_idx[LGMEMSZ-1:LGNFFT]== tidx[LGMEMSZ-1:LGNFFT]);

	always @(*)
	if (!top_of_block && !i_ce && !i_alt_ce)
		assert(f_passed_idx[LGNFFT-1:0] == 0);

	always @(*)
	begin
		f_passw_idx = lidx-dwidx;
		f_passed_diff = f_phase[LGMEMSZ+LSBPHASE-1:LSBPHASE+1]
					+ f_phase[LSBPHASE];
	end

	always @(*)
	if (!top_of_block)
	begin
		assert(f_passw_idx[LGNFFT-1:0] == f_passed_diff);
		assert(f_passw_idx < (1<<LGNFFT));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[3:0]	cvr_top_of_blocks;


	initial	cvr_top_of_blocks = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_top_of_blocks <= 0;
	else if (i_ce && top_of_block && !cvr_top_of_blocks[3])
		cvr_top_of_blocks <= cvr_top_of_blocks + 1;

	always @(*)
	begin
		cover(cvr_top_of_blocks == 1);
		cover(cvr_top_of_blocks == 1 && (&tidx[LGNFFT-1:0]));
		cover(cvr_top_of_blocks == 1 && (&tidx[LGMEMSZ-1:0]));
		cover(cvr_top_of_blocks == 2);
		cover(cvr_top_of_blocks == 3);
	end
	// }}}
`endif
// }}}
endmodule
