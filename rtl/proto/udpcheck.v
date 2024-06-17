////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/udpcheck.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Checks for UDP packets.  If it is a UDP packet, it only passes
//		it through if it has no checksum errors.  Non-UDP packets are
//	passed sans modification.  Checksum errors will result in aborted
//	packets, so the downstream knows to abort them.
//
// Status:	This module doesn't pass formal, and isn't being used by the
//		rest of the project.
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
module	udpcheck (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire		i_en,
		//
		input	wire		S_AXIN_VALID,
		output	wire		S_AXIN_READY,
		input	wire	[7:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		//
		output	wire		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	wire	[7:0]	M_AXIN_DATA,
		output	wire		M_AXIN_LAST,
		output	wire		M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	reg	[15:0]	addr, ip_len, udp_len;
	reg		udp_carry, udp_last, nomatch;
	reg	[15:0]	udp_checksum;
	reg	[5:0]	ip_hdr;

	reg		m_valid, m_last, m_abort;
	reg	[7:0]	m_data;
	// }}}

	assign	S_AXIN_READY = (!M_AXIN_VALID || M_AXIN_READY) || S_AXIN_ABORT;
	// addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		addr <= 0;
	else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
		addr <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		addr <= addr + 1;
	// }}}

	// udp_len
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && S_AXIN_READY)
	begin
		if (addr == 11)
			udp_len <= ip_len - ip_hdr;
		if (addr >= 20 && addr == 8 + ip_hdr + 5)
			udp_len <= { M_AXIN_DATA, S_AXIN_DATA };
	end
	// }}}

	// udp_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		udp_last <= 0;
	else if (S_AXIN_ABORT
		|| (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
		udp_last <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		if (addr == 7 + ip_hdr + udp_len)
			udp_last <= !nomatch;
	end
	// }}}

	// udp_carry, udp_checksum, ip_hdr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		{ udp_carry, udp_checksum } <= 0;
		ip_hdr <= 6'd20;
	end else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
	begin
		{ udp_carry, udp_checksum } <= 0;
		ip_hdr <= 6'd20;
	end else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		if (addr == 8)
			ip_hdr <= { S_AXIN_DATA[3:0], 2'b00 };
		if (addr == 10)
			ip_len[15:8] <= S_AXIN_DATA;
		if (addr == 11)
			ip_len[7:0] <= S_AXIN_DATA;
		if (addr == 13)
			{ udp_carry, udp_checksum } <= ip_len + 8'h11;
		if (addr >= 20 && addr < ip_hdr + 8 && addr < ip_hdr + 8 + udp_len)
		begin
			if (!addr[0])
				{ udp_carry, udp_checksum[15:8] } <= udp_checksum[15:8] + S_AXIN_DATA + ((udp_carry) ? 1:0);
			else
				{ udp_carry, udp_checksum[7:0] } <= udp_checksum[7:0] + S_AXIN_DATA + ((udp_carry) ? 1:0);
		end
	end
	// }}}

	// nomatch
	// {{{
	// if nomatch is true, then the checksum doesn't need to match
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		nomatch <= 0;
	end else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY))
	begin
		// No-match to if the packet checksum is zero, indicating that
		// the checksum isn't implemented.
		if ((addr >= 16)&&(addr == 8 + ip_hdr + 7))
		begin
			if (S_AXIN_DATA == 0 && M_AXIN_DATA == 0)
				nomatch <= 1;
		end

		case(addr)
		6: if (S_AXIN_DATA != 8'h08) nomatch <= 1;
		7: if (S_AXIN_DATA != 8'h00) nomatch <= 1;
		8: if (S_AXIN_DATA[7:4] != 4'h4) nomatch <= 1;
		9: if (S_AXIN_DATA != 8'h11) nomatch <= 1;
		endcase

		if (S_AXIN_LAST || S_AXIN_ABORT)
			nomatch <= 0;
	end
	// }}}

	// m_valid
	// {{{
	initial	m_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_valid <= 0;
	else if (!M_AXIN_VALID || M_AXIN_READY)
		m_valid <= S_AXIN_VALID;
	// }}}

	// m_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXIN_VALID || M_AXIN_READY)
		m_data <= S_AXIN_DATA;
	// }}}

	// m_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		m_last <= S_AXIN_LAST || udp_last;
	end
	// }}}

	assign	M_AXIN_VALID = m_valid;
	assign	M_AXIN_DATA  = m_data;
	assign	M_AXIN_LAST  = m_last;

	// M_AXIN_ABORT
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_abort <= 0;
	else if (S_AXIN_ABORT)
		m_abort <= 1;
	else if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
	begin
		if (!nomatch)
		begin
			m_abort <= ((udp_checksum + (udp_carry ? 1:0)) != 16'hffff);
			if (addr != 7 + ip_hdr + udp_len)
				m_abort <= 1;
		end
	end else if (M_AXIN_ABORT &&(!M_AXIN_VALID || M_AXIN_READY))
		m_abort <= 1'b0;

	assign	m_abort = M_AXIN_ABORT;
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
	reg		f_past_valid;
	wire	[14:0]	fmst_word, fslv_word;
	wire	[11:0]	fmst_pkts, fslv_pkts;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	faxin_slave #(
		.DATA_WIDTH(8), .MAX_LENGTH(8192), .MIN_LENGTH(8+20)
	) fslv (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		.f_stream_word(fslv_word), .f_packets_rcvd(fslv_pkts)
		// }}}
	);

	faxin_master #(
		.DATA_WIDTH(8), .MAX_LENGTH(8192), .MIN_LENGTH(12)
	) fmst (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(M_AXIN_VALID),
		.S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA),
		.S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		.f_stream_word(fmst_word), .f_packets_rcvd(fmst_pkts)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN && !nomatch && addr == 8 && S_AXIN_VALID && S_AXIN_DATA[7:4] == 4'h4)
		assume(S_AXIN_DATA[3:0] >= 5);

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(addr == fslv_word);

		if ((M_AXIN_VALID && M_AXIN_LAST) || M_AXIN_ABORT)
		begin
			if (!udp_last || !nomatch)
			begin
				assert(fslv_word == 0);
			end else if (fslv_word != 0)
				assert(fslv_word > fmst_word);
		end else begin
			assert(fmst_word + (m_valid ? 1:0) == fslv_word);
		end

		// if (addr == 7 + ip_hdr + udp_len)
		if (addr < 9)
			assert(ip_hdr == 20);
		else if (!nomatch)
			assert(ip_hdr[1:0] == 2'b00 && ip_hdr >= 20);

		if (addr < 9)
		begin
			assert(!udp_last);
			assert(ip_hdr == 20);
		end

		if (addr < 8)
			assert(!udp_last);

		if (nomatch)
		begin
			assert(!udp_last);
			assert(fslv_word > 6);
		end

		assert(nomatch || ip_hdr >= 6'd20);
	end
`endif
// }}}
endmodule
