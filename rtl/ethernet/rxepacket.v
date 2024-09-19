////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/rxepacket.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	The purpose of this module is quite simple: to simplify the
//		receive process.  By running the receive data through a
//	series of "filter" processes (of which this is one), I hope to reduce
//	the complexity of the filter design.  This particular filter determines
//	if/when to write to memory, and at what address to write to.  Further,
//	because nibbles come into the interface in LSB order, and because we
//	are storing the first byte in the MSB, we need to shuffle bytes around
//	in this interface.  Therefore, this interface is also design to make
//	certain that, no matter how many bytes come in, we have always
//	written a complete word to the output.  Hence, each word may be
//	written 8-times (once for each nibble) ... but that be as it may.
//
//	This routine also measures packet length in bytes.
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
`timescale	1ns/1ps
// }}}
module	rxepacket (
		// {{{
		// i_clk, i_reset, i_ce, i_v, i_d, o_v, o_addr, o_data, o_len);
		input	wire			i_clk, i_reset, i_abort,
		input	wire			i_v,
		input	wire	[7:0]		i_d,
		input	wire			i_not_done,
		output	reg			M_AXIN_VALID,
		input	wire			M_AXIN_READY,
		output	reg	[7:0]		M_AXIN_DATA,
		output	reg			M_AXIN_LAST,
		output	reg			M_AXIN_ABORT
		// }}}
	);

	// Signal declarations
	// {{{
	wire		r_last;
	reg		r_v, m_v;
	reg	[7:0]	r_d, m_d;
	reg		m_l;

	wire	i_done;
	// }}}

	// Delay inputs by one in order to detect last
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_abort)
		{ r_v, r_d } <= 9'h0;
	else
		{ r_v, r_d } <= { i_v, i_d };

	assign	r_last = (r_v && !i_v);
	// }}}

	// Delay inputs by one more to make sure we catch any aborts
	// {{{
	assign	i_done = !i_not_done;

	initial	{ m_v, m_d, m_l } = 0;
	always @(posedge i_clk)
	if (i_reset || i_abort)
		{ m_v, m_d, m_l } <= 0;
	else if (!M_AXIN_VALID || M_AXIN_READY || r_v)
	begin
		if (i_done || r_v)
		begin
			m_v <= r_v;
			m_d <= r_d;
			m_l <= r_last;
		end
	end
	// }}}

	// M_AXIN_VALID, M_AXIN_ABORT
	// {{{
	initial	M_AXIN_VALID = 0;
	initial	M_AXIN_ABORT = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		M_AXIN_VALID <= 0;
		M_AXIN_ABORT <= 0;
		// }}}
	end else begin // i_ce == 1
		// {{{

		// M_AXIN_ABORT
		// {{{
		// Once raised, M_AXIN_ABORT will remain raised until the
		// packet has been completed, and r_v has been lowered.
		//
		if (i_abort && (m_v || r_v))
			M_AXIN_ABORT <= 1'b1;
		else if (r_v && M_AXIN_VALID && !M_AXIN_READY)
			// *CANNOT* stall here, so drop packet on any stall
			//  Only exception is on the last item.  We can stall
			//  the last item by one cycle, hence we check for r_v
			M_AXIN_ABORT <= 1'b1;
		else if ((!M_AXIN_VALID || M_AXIN_READY)
					&& ({ m_v, r_v,i_v,i_not_done }== 4'h0))
			// Clear abort once any incoming packet ends
			M_AXIN_ABORT <= 1'b0;
		// }}}

		// M_AXIN_VALID
		// {{{
		// M_AXIN_VALID will stay high, even if M_AXIN_ABORT, until
		// the end of the packet
		//
		if (!M_AXIN_VALID || M_AXIN_READY)
			M_AXIN_VALID <= m_v && (i_done || r_v);
		// }}}
		// }}}
	end // else if i_ce != 1 (Not implemented)
	// {{{
	// if (M_AXIN_AREADY) M_AXIN_VALID <= 0;
	// if (i_abort) M_AXIN_ABORT <= 1;
	// }}}
	// }}}

	// M_AXIN_LAST, M_AXIN_DATA
	// {{{
	initial	M_AXIN_LAST  = 0;
	initial	M_AXIN_DATA  = 0;
	always @(posedge i_clk)
	if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		M_AXIN_DATA <= m_d;
		M_AXIN_LAST <= m_l;
	end
	// }}}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties used to verify this core
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	f_past_valid;
	parameter	MAX_LENGTH = 1024;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Interface assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg		i_state;
	wire	[10:0]	f_words, f_pkts, src_words;

	always @(*)
	if (i_v || i_abort)
		assume(i_not_done);

	always @(posedge i_clk)
	if (i_reset)
		i_state <= 0;
	else if (i_v)
		i_state <= 1;
	else if (i_done)
		i_state <= 0;

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_v);
	else if (!i_state)
	begin
		assume(i_v || !$rose(i_not_done));
	end else // if (i_state)
	begin
		assume(!$rose(i_v));
	end

	initial	src_words = 0;
	always @(posedge i_clk)
	if (i_reset || i_abort)
		src_words <= 0;
	else // if (i_ce)
	begin
		if (!i_v)
			src_words <= 0;
		else
			src_words <= src_words + 1;
	end

	always @(*)
	if (!r_v && (m_v || M_AXIN_VALID || i_not_done))
		assume(!i_v);

	faxin_master #(
		// {{{
		.DATA_WIDTH(8),
		.MIN_LENGTH(1)
		// }}}
	) faxin (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// i_abort
		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA),
		.S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		.f_stream_word(f_words),
		.f_packets_rcvd(f_pkts)
		// }}}
	);

	always @(*)
	begin
		assume(src_words < MAX_LENGTH);

		assert(f_words + (m_v ? 1:0) + (r_v ? 1:0) + (M_AXIN_VALID ? 1:0) < MAX_LENGTH);
	end

	always @(*)
	if (!i_reset)
	begin
		if (!M_AXIN_ABORT && i_state)
		begin
			if ((m_v && m_l)||(M_AXIN_VALID && M_AXIN_LAST))
				assert(src_words == 0);
			else
				assert(src_words == f_words
						+ (r_v ? 1:0) + (m_v ? 1:0)
						+ (M_AXIN_VALID ? 1:0));
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Last check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!i_reset && M_AXIN_VALID && i_not_done)
		assert(!M_AXIN_LAST);

	always @(posedge i_clk)
	if (!i_reset && M_AXIN_VALID && M_AXIN_LAST && !M_AXIN_ABORT)
		assert(!m_v && !r_v);

	always @(posedge i_clk)
	if (!i_reset)
		assert(m_l == (m_v && !r_v));

	always @(posedge i_clk)
	if (!i_reset && M_AXIN_VALID && M_AXIN_LAST)
		assert(!m_v && !r_v && i_done);

	always @(posedge i_clk)
	if (!i_reset && m_v && m_l)
	begin
		assert(!M_AXIN_VALID || !M_AXIN_LAST);
		assert(!r_v);
	end

	always @(posedge i_clk)
	if (!i_reset && M_AXIN_VALID && !M_AXIN_LAST && !M_AXIN_ABORT)
	begin
		assert(r_v || (m_v && m_l));
	end

	// always @(posedge i_clk)
	// if (!i_reset && !$past(i_reset) && $past(M_AXIN_VALID && !M_AXIN_

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never data
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg		f_nvr_check;
	(* anyconst *)	reg	[7:0]	f_nvr_data;

	always @(*)
	if (!i_reset && f_nvr_check)
		assume(!i_v || (i_d != f_nvr_data));

	always @(*)
	if (!i_reset && f_nvr_check && r_v)
		assert(r_d != f_nvr_data);

	always @(*)
	if (!i_reset && f_nvr_check && m_v)
		assert(m_d != f_nvr_data);

	always @(*)
	if (!i_reset && f_nvr_check && M_AXIN_VALID && !M_AXIN_ABORT)
		assert(M_AXIN_DATA != f_nvr_data);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Safety (assertion) properties
	//

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_past_valid, f_pkts };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule

