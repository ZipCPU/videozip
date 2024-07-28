////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/fftavg.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Converts FFT outputs to energy outputs.  Optionally averages
//		those outputs.  Optionally applies a max hold to those outputs.
//
// Would like to be able to discuss averaging in terms of *time*, not blocks.
// - At 1.2Msps and 1024 samples per FFT, that's 2344 FFTs per second.  A 1s
//   average would therefore be 2^11 FFTs (roughly).  A 1min average would be
//   2^17 FFTs.
// - At 100Msps and 1024 samples per FFT, that's 2^18 FFTs per second.  A 1m
//   average would be 2^24.
// - At 48kHz samples, and 1024 sampler per FFT, that's 94 FFTs per second.  A
//   1s average would be between 64 and 128 FFTs so roughly 2^7 FFTs.  A 60s
//   average would require 2^13 FFTs.
// Hence we should allow averaging between 2^0 (no averaging) and 2^31 (5bits)
//
//
// Status:
//	What about taking the log of the result?  How shall we deal with
//	large dynamic ranges?
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
module	fftavg #(
		// {{{
		parameter	IW = 12,	// Input bitwidth
		parameter	LGFFT = 10,	// Log of the FFT size
		localparam	OW = 2*IW+1,
		localparam	FFTSZ = 1<<LGFFT,
		localparam [0:0] OPT_SHARED_MPY = 1'b0
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire			i_maxhold, // i_logresult,
		input	wire	[4:0]		i_lgavg,
		input	wire			i_rmbias,
		//
		input	wire			S_AXIS_TVALID,
		output	wire			S_AXIS_TREADY,
		input	wire	[2*IW-1:0]	S_AXIS_TDATA, // I+Q data
		input	wire			S_AXIS_TLAST,
		//
		output	wire			M_AXIS_TVALID,
		input	wire			M_AXIS_TREADY,
		output	wire	[OW-1:0]	M_AXIS_TDATA, // Real data only
		output	wire			M_AXIS_TLAST
		// }}}
	);

	// Local declarations
	// {{{
	wire			skd_valid, skd_last, skd_ready, sqr_busy;
	wire	[2*IW-1:0]	skd_data;

	reg			sqr_valid, sqr_last;
	reg	[2*IW:0]	sqr_data;
	wire			sqr_ready;

	reg			av_valid, av_full, av_last;
	reg	[LGFFT-1:0]	av_wptr, av_rptr;
	reg	[2*IW:0]	av_data, av_memval;
	reg	[2*IW:0]	av_mem	[0:FFTSZ-1];
	wire			av_ready;

	reg	[2*IW+LGFFT:0]	sm_partial, sm_sum, sm_offset_wide;
	wire	[2*IW:0]	sm_offset;
	reg	[2*IW:0]	sm_premax, sm_maxvalue;
	reg			mh_valid, mh_last, mh_rv;

	reg	[LGFFT-1:0]	mh_rptr, mh_wptr;
	reg	[2*IW:0]	mh_data, mh_memval;
	reg	[2*IW:0]	mh_mem	[0:FFTSZ-1];
	wire			mh_ready;

	reg			ub_valid, ub_last;
	reg	[2*IW:0]	ub_data;
	wire			ub_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 1. Skid buffer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	localparam [0:0]	OPT_SKIDBUFFER = 1'b0;

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		skidbuffer #(
			.OPT_LOWPOWER(0), .OPT_OUTREG(0), .DW(2*IW+1)
		) ibuf(
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
			.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
				.i_data({ S_AXIS_TLAST, S_AXIS_TDATA }),
			.o_valid(skd_valid), .i_ready(skd_ready),
				.i_data({ skd_last, skd_data })
			// }}}
		);

	end else begin : NO_SKIDBUFFER
		assign	skd_valid = S_AXIS_TVALID;
		assign	S_AXIS_TREADY = skd_ready;
		assign	skd_data  = S_AXIS_TDATA;
		assign	skd_last  = S_AXIS_TLAST;
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 2. Square results, to convert from I+Q to real
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (OPT_SHARED_MPY)
	begin : GEN_SHARED_SQUARE
		// {{{
		reg	[3:0]			pipe, lpipe, mpy_last;

		wire	signed	[IW-1:0]	sgn_idata, sgn_qdata;
		reg	signed	[IW-1:0]	last_qdata, mpy_input;
		reg	signed	[2*IW-1:0]	mpy_result;

		assign	sgn_idata = skd_data[2*IW-1:IW];
		assign	sgn_qdata = skd_data[  IW-1: 0];

		// skdvalid	busy
		//	1	0
		//	!R	1
		//	RDY	0
		//		mpy_in	mpy_in
		//			mpy_prod
		//				mpy_prod
		//				sum1
		//					mpy_sum
		//
		//	skdvalid
		//	1. busy,  mpy_in (first)
		//	2. !busy, mpy_in (second), mpy_prod(first)
		//	3. mpy_prod(second), mpy_sum(first)
		//	4. mpy_sum(second)

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			pipe  <= 4'h0;
			lpipe <= 4'h0;
		end else if (skd_valid && skd_ready)
		begin
			pipe  <= { pipe[2:0],  1'b1 };
			lpipe <= { lpipe[2:0], skd_last };
		end else if (!sqr_valid || sqr_ready)
		begin
			pipe  <= { pipe[2:0],  1'b0 };
			lpipe <= { lpipe[2:0], 1'b0 };
		end

		always @(*)
		begin
			sqr_valid =  pipe[3];
			sqr_last  = lpipe[3];
		end
		assign	sqr_busy  =  pipe[0];

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			last_qdata <= 0;
		else if (skd_valid && skd_ready)
			last_qdata <= sgn_qdata;

		always @(posedge S_AXI_ACLK)
		if (!sqr_valid || sqr_ready)
			mpy_input <= (sqr_busy) ? last_qdata : sgn_idata;

		always @(posedge S_AXI_ACLK)
		if ((!sqr_valid || sqr_ready)&&(|pipe[1:0]))
			mpy_result <= mpy_input * mpy_input;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			mpy_last <= 0;
		else if ((!sqr_valid || sqr_ready)&&(pipe[1]))
			mpy_last <= mpy_result;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			sqr_data <= 0;
		else if ((!sqr_valid || sqr_ready)&&(pipe[2]))
			sqr_data <= mpy_result + mpy_last;

		assign	skd_ready = (!sqr_valid || sqr_ready)&&(!pipe[0]);
		// }}}
	end else begin : SEPARATE_SQUARE
		// {{{
		wire	signed	[IW-1:0]	sgn_idata, sgn_qdata;
		reg				prod_valid, prod_last;
		reg	signed [2*IW-1:0]	prod_idata, prod_qdata;

		assign	sqr_busy = 1'b0;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
		begin
			{ sqr_valid, prod_valid }<= 2'b00;
			{ sqr_last,  prod_last } <= 2'b00;
		end else if (skd_valid && skd_ready)
		begin
			{ sqr_valid, prod_valid }<= { prod_valid, skd_valid };
			{ sqr_last,  prod_last } <= { prod_last,  skd_last };
		end


		assign	sgn_idata = skd_data[2*IW-1:IW];
		assign	sgn_qdata = skd_data[  IW-1: 0];

		always @(posedge S_AXI_ACLK)
		if (skd_valid && skd_ready)
			prod_idata <= sgn_idata * sgn_idata;

		always @(posedge S_AXI_ACLK)
		if (skd_valid && skd_ready)
			prod_qdata <= sgn_qdata * sgn_qdata;

		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN || !prod_valid)
			sqr_data <= 0;
		else if (skd_valid && skd_ready)
			sqr_data <= prod_idata + prod_qdata;

		assign	skd_ready = (!av_valid || av_ready) && !sqr_busy;
		// }}}
	end endgenerate

	assign	sqr_ready = !av_valid || av_ready;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 3. Apply the recursive average
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// av_valid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		av_valid <= 0;
	else if (sqr_valid && sqr_ready)
		av_valid <= 1;
	else if (av_ready)
		av_valid <= 0;
	// }}}

	// av_wptr, av_full, av_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		av_wptr <= 0;
		av_full <= 0;
		av_last <= 0;
	end else if (sqr_valid && sqr_ready)
	begin
		av_last <= sqr_last;
		if (sqr_last)
			av_wptr <= 0;
		else
			av_wptr <= av_wptr + 1;
		av_full <= av_full || (&av_wptr);
	end
	// }}}

	// av_rptr -- the read pointer
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		av_rptr <= 0;
	else if (sqr_valid && sqr_ready)
		av_rptr <= av_wptr + 2;
	// }}}

	// av_memval
	// {{{
	always @(posedge S_AXI_ACLK)
	if (sqr_valid && sqr_ready)
		av_memval <= av_mem[av_rptr];
	// }}}

	// av_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (sqr_valid && sqr_ready)
	begin
		if (av_full)
			av_data <= av_memval + ((sqr_data - av_memval) >>> i_lgavg);
		else
			av_data <= sqr_data - av_memval;
	end
	// }}}

	// Write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (sqr_valid && sqr_ready)
		av_mem[av_wptr] <= av_data;
	// }}}

	assign	av_ready = !mh_valid || mh_ready;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 4. Calculate a block average, estimate max, across the whole FFT
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		sm_partial <= 0;
		sm_premax <= 0;
	end else if (av_valid && av_ready)
	begin
		if (av_last)
		begin
			sm_partial <= 0;
			sm_premax  <= 0;
		end else begin
			sm_partial <= sm_partial + { {(LGFFT){1'b0}}, av_data };
			if (av_data > sm_premax)
				sm_premax <= av_data;
		end
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		sm_sum <= 0;
	end else if (av_valid && av_ready && av_last)
	begin
		sm_sum <= sm_partial + { {(LGFFT){1'b0}}, av_data };
		if (av_data > sm_premax)
			sm_maxvalue <= av_data;
		else
			sm_maxvalue <= sm_premax;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !i_rmbias)
		sm_offset_wide <= 0;
	else
		sm_offset_wide <= sm_sum - (sm_sum >> 4);

	// Divide by the FFT size
	assign	sm_offset = sm_offset_wide[LGFFT +: 2*IW+1];
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 5. Apply the optional max hold
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//


	// Issues:
	//  - Do we try to keep the memory aligned with the FFT, or just aligned
	//    internally?

	// mh_valid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mh_valid <= 0;
	else if (av_valid && av_ready)
		mh_valid <= 1;
	else if (mh_ready)
		mh_valid <= 0;
	// }}}

	// mh_wptr, mh_rv, mh_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !i_maxhold)
	begin
		mh_wptr <= 0;
		mh_rv   <= 0;
		mh_last <= 0;
	end else if (av_valid && av_ready)
	begin
		mh_last <= av_last;
		mh_wptr <= mh_wptr + 1;
		mh_rv  <= mh_rv || (&mh_wptr);
	end
	// }}}

	// mh_rptr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !i_maxhold)
		mh_rptr <= 1;
	else if (av_valid && av_ready)
		mh_rptr <= mh_wptr + 2;
	// }}}

	// mh_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mh_data <= 0;
	else if (av_valid && av_ready)
	begin
		if (i_maxhold && mh_rv && mh_memval > av_data)
			mh_data <= mh_memval;
		else
			mh_data <= av_data;
	end
	// }}}

	// mh_mem
	// {{{
	always @(posedge S_AXI_ACLK)
	if (av_valid&& av_ready)
		mh_mem[mh_wptr] <= mh_data;
	// }}}

	// mh_memval
	// {{{
	always @(posedge S_AXI_ACLK)
	if (av_valid&& av_ready)
		mh_memval <= mh_mem[mh_rptr];
	// }}}

	assign	mh_ready = !ub_valid || ub_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 6. Remove the bias
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ ub_valid, ub_last } <= 0;
	else if (mh_valid && mh_ready)
		{ ub_valid, ub_last } <= { 1'b1, mh_last };
	else if (ub_ready)
		ub_valid <= 0;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		ub_data <= 0;
	else if (mh_valid && mh_ready)
	begin
		if (mh_data > sm_offset)
			ub_data <= mh_data - sm_offset;
		else
			ub_data <= 0;
	end

	assign	mh_ready = !ub_valid || ub_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// 7. Set the output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	M_AXIS_TVALID = ub_valid;
	assign	ub_ready = M_AXIS_TREADY;
	assign	M_AXIS_TDATA  = ub_data;
	assign	M_AXIS_TLAST  = ub_last;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, sm_offset_wide, sm_maxvalue };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
