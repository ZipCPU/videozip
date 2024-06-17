////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/arp.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Scans incoming packet stream for ARP requests, and automatically
//		transforms those requests to ARP replies when one is found.
//	The ARP reply is then sent on the outgoing network packet stream port.
//
// Incoming packet format		-> Outgoing packet format(if successful)
// {{{
//		0: SrcMAC0		Source MAC address, byte #0
//		1: SrcMAC1
//		2: SrcMAC2
//		3: SrcMAC3
//		4: SrcMAC4
//		5: SrcMAC5
//		6: ETYP0		0x08
//		7: ETYP1		0x06
//		8: HTYP0		0x00
//		9: HTYP1		0x01
//		10: PTYP0		0x08
//		11: PTYP1		0x00
//		12: HLEN		0x06
//		13: PLEN		0x04
//		14: OPER0		0x00
//		15: OPER1		0x01	-> 0x02
//		16: SHA0		SrcMAC0	-> MyMAC0
//		17: SHA1		SrcMAC1	-> MyMAC1
//		18: SHA2		SrcMAC2	-> MyMAC2
//		19: SHA3		SrcMAC3	-> MyMAC3
//		20: SHA4		SrcMAC4	-> MyMAC4
//		21: SHA5		SrcMAC5	-> MyMAC5
//		22: SPA0		SrcIP0
//		23: SPA1		SrcIP1
//		24: SPA2		SrcIP2
//		25: SPA3		SrcIP3
//		26: THA0		0xxx	-> SrcMAC0
//		27: THA1		0xxx	-> SrcMAC1
//		28: THA2		0xxx	-> SrcMAC2
//		29: THA3		0xxx	-> SrcMAC3
//		30: THA4		0xxx	-> SrcMAC4
//		31: THA5		0xxx	-> SrcMAC5
//		32: TPA0		MyIP0	-> SrcIP0
//		33: TPA1		MyIP1	-> SrcIP1
//		34: TPA2		MyIP2	-> SrcIP2
//		35: TPA3		MyIP3	-> SrcIP3 -> MATCH (or NONE)
//		36-??			0xxx	-> 0x00
// }}}
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
module	arp // #()
	(
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		// Incoming packets--may or may not be ARP requests
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
		input	wire	[47:0]	i_hwmac,
		input	wire	[31:0]	i_ipaddr,
		output	reg		o_match,
		output	reg		o_no_match,
		output	wire	[3:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	reg	[47:0]	src_mac;
	reg	[31:0]	src_ip;
	reg	[5:0]	addr;

	reg		mid_packet;

	assign	o_debug = { mid_packet, addr[5:3] };
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
	 7: if (S_AXIN_DATA != 8'h06)	o_no_match <= 1;
	 8: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	 9: if (S_AXIN_DATA != 8'h01)	o_no_match <= 1;
	10: if (S_AXIN_DATA != 8'h08)	o_no_match <= 1;
	11: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	12: if (S_AXIN_DATA != 8'h06)	o_no_match <= 1;
	13: if (S_AXIN_DATA != 8'h04)	o_no_match <= 1;
	14: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	15: if (S_AXIN_DATA != 8'h01)	o_no_match <= 1;
	16: if (S_AXIN_DATA != src_mac[47:40])	o_no_match <= 1;
	17: if (S_AXIN_DATA != src_mac[39:32])	o_no_match <= 1;
	18: if (S_AXIN_DATA != src_mac[31:24])	o_no_match <= 1;
	19: if (S_AXIN_DATA != src_mac[23:16])	o_no_match <= 1;
	20: if (S_AXIN_DATA != src_mac[15: 8])	o_no_match <= 1;
	21: if (S_AXIN_DATA != src_mac[ 7: 0])	o_no_match <= 1;
	32: if (S_AXIN_DATA != i_ipaddr[31:24])	o_no_match <= 1;
	33: if (S_AXIN_DATA != i_ipaddr[23:16])	o_no_match <= 1;
	34: if (S_AXIN_DATA != i_ipaddr[15: 8])	o_no_match <= 1;
	35: if (S_AXIN_DATA != i_ipaddr[ 7: 0])	o_no_match <= 1;
					else	o_match <= !o_no_match;
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (addr >= 36)
			assert(o_match || o_no_match);

		if (addr > 0 && addr < 36)
			assert(!o_match);

		assert(!o_match || !o_no_match);

		if (!mid_packet)
			assert(!o_match && !o_no_match);
	end
`endif
	// }}}

	// src_mac
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && S_AXIN_READY && (addr < 6))
		src_mac <= { src_mac[39:0], S_AXIN_DATA };
	// }}}

	// src_ip
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && S_AXIN_READY && (addr < 26))
		src_ip <= { src_ip[23:0], S_AXIN_DATA };
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
	case(addr)
	15: M_AXIN_DATA <= 8'h02;
	16: M_AXIN_DATA <= i_hwmac[47:40];
	17: M_AXIN_DATA <= i_hwmac[39:32];
	18: M_AXIN_DATA <= i_hwmac[31:24];
	19: M_AXIN_DATA <= i_hwmac[23:16];
	20: M_AXIN_DATA <= i_hwmac[15: 8];
	21: M_AXIN_DATA <= i_hwmac[ 7: 0];
	22: M_AXIN_DATA <= i_ipaddr[31:24];
	23: M_AXIN_DATA <= i_ipaddr[23:16];
	24: M_AXIN_DATA <= i_ipaddr[15: 8];
	25: M_AXIN_DATA <= i_ipaddr[ 7: 0];
	26: M_AXIN_DATA <= src_mac[47:40];
	27: M_AXIN_DATA <= src_mac[39:32];
	28: M_AXIN_DATA <= src_mac[31:24];
	29: M_AXIN_DATA <= src_mac[23:16];
	30: M_AXIN_DATA <= src_mac[15: 8];
	31: M_AXIN_DATA <= src_mac[ 7: 0];
	32: M_AXIN_DATA <= src_ip[31:24];
	33: M_AXIN_DATA <= src_ip[23:16];
	34: M_AXIN_DATA <= src_ip[15: 8];
	35: M_AXIN_DATA <= src_ip[ 7: 0];
	default: if (addr >= 36)
			M_AXIN_DATA <= 8'h0;
		else
			M_AXIN_DATA <= S_AXIN_DATA;
	endcase
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

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge S_AXI_ACLK)
		assume($stable(i_hwmac));

	always @(posedge S_AXI_ACLK)
		assume($stable(i_ipaddr));
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

	// Assume a valid packet coming in
	// {{{
	always @(*)
	if (f_check_pkt && S_AXIN_VALID && !S_AXIN_ABORT)
	case(addr)
	0: assume(S_AXIN_DATA == f_src_hwmac[47:40]);
	1: assume(S_AXIN_DATA == f_src_hwmac[39:32]);
	2: assume(S_AXIN_DATA == f_src_hwmac[31:24]);
	3: assume(S_AXIN_DATA == f_src_hwmac[23:16]);
	4: assume(S_AXIN_DATA == f_src_hwmac[15: 8]);
	5: assume(S_AXIN_DATA == f_src_hwmac[ 7: 0]);
	6: assume(S_AXIN_DATA == 8'h08);
	7: assume(S_AXIN_DATA == 8'h06);
	8: assume(S_AXIN_DATA == 8'h00);
	9: assume(S_AXIN_DATA == 8'h01);
	10: assume(S_AXIN_DATA == 8'h08);
	11: assume(S_AXIN_DATA == 8'h00);
	12: assume(S_AXIN_DATA == 8'h06);
	13: assume(S_AXIN_DATA == 8'h04);
	14: assume(S_AXIN_DATA == 8'h00);
	15: assume(S_AXIN_DATA == 8'h01);
	16: assume(S_AXIN_DATA == f_src_hwmac[47:40]);
	17: assume(S_AXIN_DATA == f_src_hwmac[39:32]);
	18: assume(S_AXIN_DATA == f_src_hwmac[31:24]);
	19: assume(S_AXIN_DATA == f_src_hwmac[23:16]);
	20: assume(S_AXIN_DATA == f_src_hwmac[15: 8]);
	21: assume(S_AXIN_DATA == f_src_hwmac[ 7: 0]);
	22: assume(S_AXIN_DATA == f_src_ipaddr[31:24]);
	23: assume(S_AXIN_DATA == f_src_ipaddr[23:16]);
	24: assume(S_AXIN_DATA == f_src_ipaddr[15: 8]);
	25: assume(S_AXIN_DATA == f_src_ipaddr[ 7: 0]);
	// 26,27,28,29,30,31 --> don't care
	32: assume(S_AXIN_DATA == i_ipaddr[31:24]);
	33: assume(S_AXIN_DATA == i_ipaddr[23:16]);
	34: assume(S_AXIN_DATA == i_ipaddr[15: 8]);
	35: assume(S_AXIN_DATA == i_ipaddr[ 7: 0]);
	endcase
	// }}}

	// Check the src mac
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && f_check_pkt)
	begin
		case(addr)
		0: begin end
		1: assert(src_mac[ 7:0] == f_src_hwmac[47:40]);
		2: assert(src_mac[15:0] == f_src_hwmac[47:32]);
		3: assert(src_mac[23:0] == f_src_hwmac[47:24]);
		4: assert(src_mac[31:0] == f_src_hwmac[47:16]);
		5: assert(src_mac[39:0] == f_src_hwmac[47: 8]);
		default:
			assert(src_mac[47:0] == f_src_hwmac[47:0]);
		endcase
	end
	// }}}

	// Check the src IP address
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && f_check_pkt)
	begin
		case(addr)
		23: assert(src_ip[ 7:0] == f_src_ipaddr[31:24]);
		24: assert(src_ip[15:0] == f_src_ipaddr[31:16]);
		25: assert(src_ip[23:0] == f_src_ipaddr[31: 8]);
		default: if (addr >= 26)
			assert(src_ip[31:0] == f_src_ipaddr[31:0]);
		endcase
	end
	// }}}

	// Assert the correct packet going out
	// {{{
	always @(*)
	if (S_AXI_ARESETN && f_check_pkt && M_AXIN_VALID && !M_AXIN_ABORT)
	case(f_addr)
	0: assert(M_AXIN_DATA == f_src_hwmac[47:40]);
	1: assert(M_AXIN_DATA == f_src_hwmac[39:32]);
	2: assert(M_AXIN_DATA == f_src_hwmac[31:24]);
	3: assert(M_AXIN_DATA == f_src_hwmac[23:16]);
	4: assert(M_AXIN_DATA == f_src_hwmac[15: 8]);
	5: assert(M_AXIN_DATA == f_src_hwmac[ 7: 0]);
	6: assert(M_AXIN_DATA == 8'h08);
	7: assert(M_AXIN_DATA == 8'h06);
	8: assert(M_AXIN_DATA == 8'h00);
	9: assert(M_AXIN_DATA == 8'h01);
	10: assert(M_AXIN_DATA == 8'h08);
	11: assert(M_AXIN_DATA == 8'h00);
	12: assert(M_AXIN_DATA == 8'h06);
	13: assert(M_AXIN_DATA == 8'h04);
	14: assert(M_AXIN_DATA == 8'h00);
	15: assert(M_AXIN_DATA == 8'h02);
	16: assert(M_AXIN_DATA == i_hwmac[47:40]);
	17: assert(M_AXIN_DATA == i_hwmac[39:32]);
	18: assert(M_AXIN_DATA == i_hwmac[31:24]);
	19: assert(M_AXIN_DATA == i_hwmac[23:16]);
	20: assert(M_AXIN_DATA == i_hwmac[15: 8]);
	21: assert(M_AXIN_DATA == i_hwmac[ 7: 0]);
	22: assert(M_AXIN_DATA == i_ipaddr[31:24]);
	23: assert(M_AXIN_DATA == i_ipaddr[23:16]);
	24: assert(M_AXIN_DATA == i_ipaddr[15: 8]);
	25: assert(M_AXIN_DATA == i_ipaddr[ 7: 0]);
	26: assert(M_AXIN_DATA == f_src_hwmac[47:40]);
	27: assert(M_AXIN_DATA == f_src_hwmac[39:32]);
	28: assert(M_AXIN_DATA == f_src_hwmac[31:24]);
	29: assert(M_AXIN_DATA == f_src_hwmac[23:16]);
	30: assert(M_AXIN_DATA == f_src_hwmac[15: 8]);
	31: assert(M_AXIN_DATA == f_src_hwmac[ 7: 0]);
	32: assert(M_AXIN_DATA == f_src_ipaddr[31:24]);
	33: assert(M_AXIN_DATA == f_src_ipaddr[23:16]);
	34: assert(M_AXIN_DATA == f_src_ipaddr[15: 8]);
	35: assert(M_AXIN_DATA == f_src_ipaddr[ 7: 0]);
	default: if (f_addr >= 36)
		assert(M_AXIN_DATA == 8'h00);
	endcase
	// }}}

	always @(*)
	if (f_check_pkt)
	begin
		if (f_addr >= 36)
			assert(o_match || M_AXIN_LAST || M_AXIN_ABORT || addr == 0);
		assert(!o_no_match);
	end

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
