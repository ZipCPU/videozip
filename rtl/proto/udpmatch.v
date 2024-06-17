////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/udpmatch.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Scans incoming packet stream for UDP requests to a particular
//		port, and forwards the request(s) forward if they match.
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
module	udpmatch // #()
	(
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		// Incoming packets--may or may not be UDP requests
		// {{{
		input	wire		S_AXIN_VALID,
		output	reg		S_AXIN_READY,
		input	wire	[7:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		// }}}
		// Outgoing packet interface
		// {{{
		output	reg		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	reg	[7:0]	M_AXIN_DATA,
		output	reg		M_AXIN_LAST,
		output	reg		M_AXIN_ABORT,
		// }}}
		// Configuration interface
		input	wire	[15:0]	i_udpport,
		output	reg		o_match,
		output	reg		o_no_match
		// }}}
	);

	// Local declarations
	// {{{
	reg	[5:0]	addr;

	reg		mid_packet;
	// }}}

	// S_AXIN_READY
	// {{{
	always @(*)
		S_AXIN_READY = M_AXIN_READY || !M_AXIN_VALID || o_no_match;
	// }}}

	// mid_packet
	// {{{
	// Based on the source interface alone
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mid_packet <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		mid_packet <= !S_AXIN_ABORT && !S_AXIN_LAST;
	else if (!S_AXIN_VALID && S_AXIN_ABORT)
		mid_packet <= 0;
	// }}}

	// M_AXIN_VALID
	// {{{
	initial	M_AXIN_VALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_VALID <= 0;
	else if (!M_AXIN_VALID || M_AXIN_READY)
		M_AXIN_VALID <= S_AXIN_VALID && !o_no_match;
	// }}}

	// M_AXIN_ABORT
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_ABORT <= 0;
	else if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		if (!mid_packet)
			M_AXIN_ABORT <= 0;

		if (mid_packet || S_AXIN_VALID)
		begin
			if (o_no_match)
				M_AXIN_ABORT <= 1;
			if (S_AXIN_ABORT)
				M_AXIN_ABORT <= 1;
			if (S_AXIN_VALID && S_AXIN_LAST && (addr < 35))
				M_AXIN_ABORT <= 1;
		end
	end else if ((S_AXIN_ABORT || o_no_match) && mid_packet)
		M_AXIN_ABORT <= 1;
	// }}}

	// addr
	// {{{
	// Based on the source interface alone (again)
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		addr <= 0;
	else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
		addr <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY && (addr < 40))
		addr <= addr + 1;
	// }}}

	// o_no_match, o_match
	// {{{
	initial { o_no_match, o_match } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ o_no_match, o_match } <= 0;
	else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
		{ o_no_match, o_match } <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
	case(addr)
	 6: if (S_AXIN_DATA != 8'h08)	o_no_match <= 1;
	 7: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	 8: if (S_AXIN_DATA != 8'h45)	o_no_match <= 1;	// IPv4, HDR=5
	//
	14: if (S_AXIN_DATA[4:0] != 5'h0 || S_AXIN_DATA[7])
		o_no_match <= 1; // No fragments allowed
	15: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;	// No fragments
	17: if (S_AXIN_DATA != 8'h11)	o_no_match <= 1;	// Must be UDP
	//
	30: if (S_AXIN_DATA != i_udpport[15:8])	o_no_match <= 1; // Must match
	31: if (S_AXIN_DATA != i_udpport[7:0])	o_no_match <= 1; // our UDP port
		else
			o_match <= !o_no_match;
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (addr >= 32)
			assert(o_match || o_no_match);

		if (addr > 0 && addr < 32)
			assert(!o_match);

		assert(!o_match || !o_no_match);

		if (!mid_packet)
			assert(!o_match && !o_no_match);
	end
`endif
	// }}}

	// M_AXIN_LAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXIN_VALID || M_AXIN_READY)
		M_AXIN_LAST <= S_AXIN_LAST;
	// }}}

	// M_AXIN_DATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && (!M_AXIN_VALID || M_AXIN_READY))
		M_AXIN_DATA <= S_AXIN_DATA;
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
	reg	f_past_valid;
	wire	[10:0]	s_words, m_words;
	(* anyconst *) reg	f_never_abort;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(posedge S_AXI_ACLK)
		assume($stable(i_udpport));

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never abort checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (f_never_abort)
	begin
		assume(!S_AXIN_ABORT);
		assume(!o_no_match);
		if (M_AXIN_VALID)
			assume(M_AXIN_READY);
		if (S_AXIN_VALID && s_words < 35)
			assume(!S_AXIN_LAST);

		if (S_AXI_ARESETN)
			assert(!M_AXIN_ABORT);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		.DATA_WIDTH(8),
		.MIN_LENGTH(24)
	) fslv (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),

		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA( S_AXIN_DATA),
		.S_AXIN_LAST( S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),

		.f_stream_word(s_words)
		// }}}
	);

	faxin_master #(
		.DATA_WIDTH(8),
		.MIN_LENGTH(24)
	) fmst (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),

		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA( M_AXIN_DATA),
		.S_AXIN_LAST( M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),

		.f_stream_word(m_words)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		assert(S_AXIN_ABORT || mid_packet == (s_words != 0));

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && M_AXIN_VALID)
		assert((M_AXIN_ABORT || M_AXIN_LAST) || addr > 0);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && (!S_AXIN_VALID || !S_AXIN_ABORT))
	begin
		assert(mid_packet == (addr > 0));
		assert(mid_packet == (s_words > 0));
		if (addr < 40)
			assert(addr == s_words);
		else
			assert(addr == 40);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && !M_AXIN_ABORT)
	begin
		if (addr < 40)
			assert(s_words == addr);
		else begin
			assert(addr == 40);
			assert(s_words >= addr);
		end

		if (M_AXIN_VALID && M_AXIN_LAST)
			assert(s_words == 0);

		if (s_words > 0)
		begin
			assert(m_words + (M_AXIN_VALID ? 1:0) == s_words);
		end else if (m_words != 0)
		begin
			assert(M_AXIN_VALID && M_AXIN_LAST);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg		f_check_pkt;
	(* anyconst *)	reg	[47:0]	f_src_hwmac;
	(* anyconst *)	reg	[31:0]	f_src_ipaddr;
	reg	[5:0]	f_addr;

	initial	f_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_addr <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		f_addr <= addr;

	/*
	always @(*)
	if (f_check_pkt)
	begin
		if (f_addr >= 32)
			assert(o_match || M_AXIN_LAST || M_AXIN_ABORT || addr == 0);
		assert(!o_no_match);
	end
	*/

	always @(*)
	if (S_AXI_ARESETN && !M_AXIN_ABORT && addr > 0 && addr < 40)
		assert(addr == f_addr + 1);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		cover(f_check_pkt && M_AXIN_VALID && M_AXIN_LAST
			&& !M_AXIN_ABORT && f_addr == 35);
	end
	// }}}
`endif
// }}}
endmodule
