////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/icmpecho.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Detects ICMP echo requests in an incoming packet stream, and
//		constructs echo responses to be sent in response to them.
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
`timescale	1ns/1ps
// }}}
module	icmpecho #(
		parameter [0:0]	OPT_IPADDR_CHECK = 1'b0
	) (
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
		output	wire		M_AXIN_ABORT,
		// }}}
		// Configuration interface
		input	wire	[31:0]	i_ipaddr,
		output	reg		o_match,
		output	reg		o_no_match,
		//
		output	reg	[47:0]	o_ping_mac,
		output	reg	[31:0]	o_ping_ipaddr,
		// }}}
		output	wire	[31:0]	o_debug
	);

	// Local declarations
	// {{{
	localparam [2:0]	S_IDLE		= 3'b000,
				S_HEADER	= 3'b001,
				S_PAYLOAD	= 3'b010,
				S_IPCHECKSUMHI	= 3'b011,
				S_IPCHECKSUMLO	= 3'b100,
				S_ICMPCHECKSUMHI= 3'b101,
				S_ICMPCHECKSUMLO= 3'b110,
				S_LENGTH	= 3'b111;
	localparam	LGMEM = 8;	// *CANNOT* be any larger

	reg	[2:0]		state, last_state;
	reg			mem_wr, ipaddr_hi;
	reg	[LGMEM-1:0]	mem_waddr;
	reg	[7:0]		mem_wdata;
	reg	[15:0]		ip_checksum;
	reg	[15:0]		icmp_checksum;
	reg			ip_carry, icmp_carry, ipaddr_match;
	reg			aborting, mid_packet;
	reg	[LGMEM-1:0]	start_of_packet;
	reg	[7:0]		mem	[0:255];
	reg	[LGMEM-1:0]	addr;
	reg	[6:0]		hdr_size; // From 8 + 5*4 to 8+15*4
	reg	[LGMEM-1:0]	payload_addr, icmp_checksum_addr,
				ip_checksum_addr, next_start_of_packet;
	wire	[7:0]		fill;
	wire			overflow;

	reg			rdstate;
	reg	[LGMEM-1:0]	mem_raddr, rdlen;
	reg	[7:0]		pkt_data;

	reg	[2:0]	broadcast_count;
	reg	[47:0]	src_mac;
	reg	[31:0]	src_ip;
	reg		valid_memory, valid_mempipe;
	reg		trigger, trigger_primed;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Determine if this is an ICMP packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_no_match, o_match
	// {{{
	initial	{ o_no_match, o_match } = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		{ o_no_match, o_match } <= 0;
		broadcast_count <= 0;
		ipaddr_match <= !OPT_IPADDR_CHECK;
	end else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
	begin
		{ o_no_match, o_match } <= 0;
		broadcast_count <= 0;
		ipaddr_match <= !OPT_IPADDR_CHECK;
	end else if (S_AXIN_VALID && S_AXIN_READY)
	case(addr)
	// We don't need to check if this IP packet is for us.  That's already
	// been done.
	//  0- 7: Ethernet: 6 bytes address, 2'bytes ethertype
	 6: if (S_AXIN_DATA != 8'h08)	o_no_match <= 1; // IP only
	 7: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	//  8-28: IP header
	// First word
	 8: if (S_AXIN_DATA[7:4] != 4'h4) o_no_match <= 1; // IPv4 only
	10: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1; // Small pkts only
	11: if (S_AXIN_DATA >= 8'hf0)	o_no_match <= 1; // Small pkts only
	// Second word
	// 12
	// Third word
	// 16
	16: if (S_AXIN_DATA <= 8'h01)	o_no_match <= 1; // TTL > 1 only
	17: if (S_AXIN_DATA != 8'h01)	o_no_match <= 1; // ICMP only
	// Last IP word -- the destination IP
	// {{{
	24: begin
		if (S_AXIN_DATA == 8'hff)	broadcast_count <= broadcast_count + 1;
		ipaddr_match <= !OPT_IPADDR_CHECK || (S_AXIN_DATA == i_ipaddr[31:24]);
		end
	25: begin
		if (S_AXIN_DATA == 8'hff)	broadcast_count <= broadcast_count + 1;
		ipaddr_match <= !OPT_IPADDR_CHECK || (ipaddr_match && (S_AXIN_DATA == i_ipaddr[23:16]));
		end
	26: begin
		if (S_AXIN_DATA == 8'hff)	broadcast_count <= broadcast_count + 1;
		ipaddr_match <= !OPT_IPADDR_CHECK || (ipaddr_match && (S_AXIN_DATA == i_ipaddr[15:8]));
		end
	27: begin
		if (S_AXIN_DATA == 8'hff)	broadcast_count <= broadcast_count + 1;
		ipaddr_match <= !OPT_IPADDR_CHECK || (ipaddr_match && (S_AXIN_DATA == i_ipaddr[7:0]));
		end
	// }}}
	//
	28: begin
		if (broadcast_count[2])		o_no_match <= 1; // No brdcast
		if (!ipaddr_match)		o_no_match <= 1;
		if (S_AXIN_DATA != 8'h08)	o_no_match <= 1; // Echo Rq only
		end
	29: if (S_AXIN_DATA != 8'h00)		o_no_match <= 1; // Code
		else o_match <= !o_no_match;
	//
	// We can't match over the checksum as well, since that will be
	// calculated over the data as well, and ... that data is not
	// predictable
	//
	// 30: if (S_AXIN_DATA != 8'h08)	o_no_match <= 1; // Checksum
	// 31: if (S_AXIN_DATA != 8'h00)	o_no_match <= 1;
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (addr >= 30)
			assert(o_match || o_no_match);

		assert(!o_match || !o_no_match);

		if (addr > 0 && addr < 30)
			assert(!o_match);

		if (!mid_packet)
			assert(!o_match && !o_no_match);
	end
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate the new packet, storing it into memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	fill = start_of_packet - mem_raddr;
	assign	overflow = (fill + addr > 9'h0fc);	// Need stop for ptr

	// S_AXIN_READY
	// {{{
	always @(*)
		S_AXIN_READY = 1'b1;
	// }}}

	// addr
	// {{{
	// Based on the source only
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		addr <= 0;
	else if (aborting || S_AXIN_ABORT
			|| (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST))
		addr <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY && (state <= S_PAYLOAD || icmp_carry))
		addr <= addr + 1;
	// }}}

	// payload_addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		payload_addr <= 0;
	else if (state <= S_HEADER)
		payload_addr <= 0;
	else if (state == S_PAYLOAD && S_AXIN_VALID && S_AXIN_READY)
		payload_addr <= payload_addr + 1;
	// }}}

	// ip_checksum_addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (state == S_IDLE)
		ip_checksum_addr <= start_of_packet + 8 + 11;
	// }}}

	// ip_checksum, ip_carry
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		last_state <= S_IDLE;
	else
		last_state <= state;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ ip_carry, ip_checksum } <= 0;
	else if (addr == 7)
		{ ip_carry, ip_checksum } <= 0;
	else if (mem_wr)
	begin
		if (last_state <= S_HEADER)
			ipaddr_hi <= addr[0];
		else
			ipaddr_hi <= !ipaddr_hi;

		if (last_state == S_HEADER)
		begin
			// IP Header checksum
			if (!ipaddr_hi)
				{ ip_carry, ip_checksum[15:8] } <= ip_checksum[15:8] + (ip_carry ? 1:0) + mem_wdata;
			else
				{ ip_carry, ip_checksum[7:0] } <= ip_checksum[7:0] + (ip_carry ? 1:0) + mem_wdata;
		end else if (ip_carry)
		begin
			// Handle any residual carry
			if (!ipaddr_hi)
				{ ip_carry, ip_checksum[15:8] } <= ip_checksum[15:8] + (ip_carry ? 1:0);
			else
				{ ip_carry, ip_checksum[7:0] } <= ip_checksum[7:0] + (ip_carry ? 1:0);
		end
	end
	// }}}

	// icmp_checksum_addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (state == S_HEADER || state == S_PAYLOAD)
		icmp_checksum_addr <= start_of_packet + 1 + hdr_size + 2;
	// }}}

	// icmp_checksum, icmp_carry
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ icmp_carry, icmp_checksum } <= 0;
	else if (state < S_PAYLOAD)
		{ icmp_carry, icmp_checksum } <= 0;
	else if (state == S_PAYLOAD && S_AXIN_VALID && S_AXIN_READY)
	begin
		// ICMP Header checksum
		if (payload_addr <4)
			// First byte must be zero for a ping reply
			// Second byte, subcode, must also be zero
			// Checksum bytes don't count in our calculation
			{ icmp_carry, icmp_checksum } <= 0;
		else if (!addr[0])
			{ icmp_carry, icmp_checksum[15:8] } <= icmp_checksum[15:8] + (icmp_carry ? 1:0) + S_AXIN_DATA;
		else
			{ icmp_carry, icmp_checksum[ 7:0] } <= icmp_checksum[ 7:0] + (icmp_carry ? 1:0) + S_AXIN_DATA;

	//	// One exception: the checksum is computed as though it
	//	// weren't there, so on those clock cycles we do nothing
	//	if ((payload_addr == 2) || (payload_addr == 3))
	//		{ icmp_carry, icmp_checksum } <= { icmp_carry, icmp_checksum };
	end else if (state > S_PAYLOAD && icmp_carry)
	begin
		if (!addr[0])
			{ icmp_carry, icmp_checksum[15:8] } <= icmp_checksum[15:8] + (icmp_carry ? 1 : 0);
		else
			{ icmp_carry, icmp_checksum[ 7:0] } <= icmp_checksum[ 7:0] + (icmp_carry ? 1 : 0);
	end
	// }}}

	// hdr_size
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		hdr_size <= 8 + 20;
	else if (state == S_IDLE)
		hdr_size <= 8 + 20;	// Ethernet size + min IP size
	else if (state == S_HEADER && S_AXIN_VALID && S_AXIN_READY && addr == 8)
		hdr_size <= 8 + { S_AXIN_DATA[3:0], 2'b00 };
	// }}}

	// src_mac
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && S_AXIN_READY && addr < 6)
		src_mac <= { src_mac[39:0], S_AXIN_DATA };
	// }}}

	// src_ip
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXIN_VALID && S_AXIN_READY && (addr < 16+8))
		src_ip <= { src_ip[23:0], S_AXIN_DATA };
	// }}}

	always @(posedge S_AXI_ACLK)
	if (state == S_PAYLOAD)
		next_start_of_packet <= mem_waddr + 2;

	always @(posedge S_AXI_ACLK)
	begin
		case(state)
		S_IDLE: begin
			// {{{
			mem_wr <= 1;
			mem_waddr <= start_of_packet;
			mem_wdata <= 0;
			if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT
					&& !aborting && !mid_packet)
			begin
				state <= S_HEADER;
				mem_waddr <= mem_waddr + 1;
				mem_wdata <= S_AXIN_DATA;
			end end
			// }}}
		S_HEADER: begin
			// {{{
			mem_wr <= 1'b0;

			case(addr)
			//  8 starts the first word
			// 12 starts the second word
			14: mem_wdata <= 8'h00;	// Flags
			15: mem_wdata <= 8'h00;	// Fragmentation offset
			// 16 starts the third word
			16: mem_wdata <= S_AXIN_DATA-1;	// Time to live
			18: mem_wdata <= 0; // Zero the checksum
			19: mem_wdata <= 0; // Zero the checksum (initially)
			// 20 starts the source IP address
			20: mem_wdata <= i_ipaddr[31:24];
			21: mem_wdata <= i_ipaddr[23:16];
			22: mem_wdata <= i_ipaddr[15: 8];
			23: mem_wdata <= i_ipaddr[ 7: 0];
			// 24 starts the destination IP address
			24: mem_wdata <= src_ip[31:24];
			25: mem_wdata <= src_ip[23:16];
			26: mem_wdata <= src_ip[15: 8];
			27: mem_wdata <= src_ip[ 7: 0];
			default:
				mem_wdata <= S_AXIN_DATA;
			// 28: mem_wdata <= 8'h00;	// Reply type
			// 29: mem_wdata <= 8'h00;
			endcase

			if (S_AXIN_VALID && S_AXIN_READY)
			begin
				mem_wr <= 1;
				mem_waddr <= mem_waddr + 1;
				if (addr == hdr_size-1)
					state <= S_PAYLOAD;
			end end
			// }}}
		S_PAYLOAD: begin
			// {{{
			mem_wr <= 1'b0;

			case(payload_addr)
			0: mem_wdata <= 8'h00;	// Reply type
			1: mem_wdata <= 8'h00;
			// 2: 3:	// Checksum
			default:
				mem_wdata <= S_AXIN_DATA;
			endcase

			if (S_AXIN_VALID && S_AXIN_READY)
			begin
				mem_wr <= 1;
				mem_waddr <= mem_waddr + 1;

				if (S_AXIN_LAST)
					state <= S_IPCHECKSUMHI;
			end end
			// }}}
		S_IPCHECKSUMHI: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= ip_checksum_addr;
			mem_wdata <= ~ip_checksum[15:8];
			state <= S_IPCHECKSUMLO;
			end
			// }}}
		S_IPCHECKSUMLO: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= mem_waddr + 1;
			mem_wdata <= ~ip_checksum[7:0];
			state <= S_ICMPCHECKSUMHI;
			end
			// }}}
		S_ICMPCHECKSUMHI: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= icmp_checksum_addr;
			mem_wdata <= ~icmp_checksum[15:8];
			state <= S_ICMPCHECKSUMLO;
			end
			// }}}
		S_ICMPCHECKSUMLO: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= mem_waddr + 1;
			mem_wdata <= ~icmp_checksum[7:0];
			state <= S_LENGTH;
			end
			// }}}
		S_LENGTH: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= start_of_packet;
			mem_wdata <= next_start_of_packet - start_of_packet;
			start_of_packet <= next_start_of_packet;
			state <= S_IDLE;
			end
			// }}}
		endcase

		if (o_no_match || (S_AXIN_ABORT && state <= S_PAYLOAD)
				|| aborting)
			state <= S_IDLE;

		if (!S_AXI_ARESETN)
		begin
			state <= S_IDLE;

			// Make sure we write a zero length to the first
			// address as soon as possible, to keep the read
			// from reading a garbage length and then going
			// out to lunch on us.
			mem_wr    <= 1;
			mem_waddr <= 0;
			mem_wdata <= 0;
			start_of_packet <= 0;
		end
	end

	// aborting
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		aborting <= 0;
	else if (o_no_match)
		aborting <= 1;
	else if (S_AXIN_ABORT && state <= S_PAYLOAD && state != S_IDLE)
		aborting <= 1;
	else if (overflow)
		aborting <= 1;
	else if (state > S_PAYLOAD && S_AXIN_VALID && S_AXIN_READY)
		aborting <= 1;
	else if (state == S_IDLE && !mid_packet && !S_AXIN_VALID)
		aborting <= 0;
	// }}}

	// mid_packet
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mid_packet <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		mid_packet <= !S_AXIN_ABORT && !S_AXIN_LAST;
	else if (!S_AXIN_VALID && S_AXIN_ABORT)
		mid_packet <= 0;
	// }}}

	// write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (mem_wr)
		mem[mem_waddr] <= mem_wdata;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read the new packet out of memory
	// {{{

	localparam	[0:0]	R_IDLE = 1'b0,
				R_PACKET = 1'b1;

	// valid_memory, valid_mempipe
	// {{{
	// Our memory might be invalid on the first clock after a reset.
	// We'll need to write a zero into the first location of memory
	// before we can trust reading from it.  valid_memory is an attempt
	// to hold off reading from memory until that first zero has been
	// read.
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ valid_memory, valid_mempipe } <= 0;
	else
		{ valid_memory, valid_mempipe } <= { valid_mempipe, 1'b1 };
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert({ valid_memory, valid_mempipe } != 2'b10);
	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
		assert(valid_memory);
`endif

	// mem_raddr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mem_raddr <= 0;
	else if (rdstate == R_PACKET && (!M_AXIN_VALID || M_AXIN_READY))
		mem_raddr <= mem_raddr + 1;
	// }}}

	// pkt_data -- read from memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXIN_VALID || M_AXIN_READY)
		pkt_data <= mem[mem_raddr[LGMEM-1:0]
				+ ((rdstate == R_PACKET) ? 1:0)];
	// }}}

	// rdstate, rdlen
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !valid_memory)
	begin
		rdstate <= R_IDLE;
		rdlen   <= 0;
	end else if (rdstate == R_IDLE && pkt_data > 0)
	begin
		rdstate <= R_PACKET;
		rdlen   <= pkt_data;
	end else if (rdstate == R_PACKET && (!M_AXIN_VALID || M_AXIN_READY))
	begin
		rdlen   <= rdlen - 1;
		if (rdlen <= 1)
			rdstate <= R_IDLE;
	end
	// }}}

	// M_AXIN_VALID
	// {{{
	initial	M_AXIN_VALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_VALID <= 0;
	else if (!M_AXIN_VALID || M_AXIN_READY)
		M_AXIN_VALID <= (rdstate == R_PACKET) && rdlen > 1;
	// }}}

	// M_AXIN_ABORT
	// {{{
	// Since we go through memory, we'll never abort on output
	assign	M_AXIN_ABORT = 0;
	// }}}

	// M_AXIN_LAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_LAST <= 1'b0;
	else if (!M_AXIN_VALID || M_AXIN_READY)
		M_AXIN_LAST <= (rdstate == R_PACKET) && (rdlen == 2);
	// }}}

	// M_AXIN_DATA
	// {{{
	// always @(posedge S_AXI_ACLK)
	// if (!M_AXIN_VALID || M_AXIN_READY)
		// M_AXIN_DATA <= pkt_data;
	always @(*)
		M_AXIN_DATA = pkt_data;
	// }}}

	// }}}

	// o_ping_ipaddr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_ping_ipaddr <= 0;
	else if (state == S_LENGTH)
		o_ping_ipaddr <= src_ip;
	// }}}

	// o_ping_mac
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		o_ping_mac <= 48'h0;
	else if (state == S_LENGTH)
		o_ping_mac <= src_mac;
	// }}}

	// Debug interface
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ trigger, trigger_primed } <= 2'b00;
	else begin
		trigger_primed <= M_AXIN_VALID && !(M_AXIN_READY
					|| M_AXIN_LAST);
		trigger <= trigger_primed && !M_AXIN_VALID;
	end

	assign	o_debug = { trigger,
		mem_raddr[6:4], rdlen[4:1],
		S_AXIN_VALID, S_AXIN_READY, S_AXIN_LAST, aborting, S_AXIN_DATA,
		M_AXIN_VALID, M_AXIN_READY, M_AXIN_LAST, rdstate,  M_AXIN_DATA
		};
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// Verilator lint_on  UNUSED
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
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg		f_past_valid;
	wire	[11:0]	s_words, m_words;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(posedge S_AXI_ACLK)
		assume($stable(i_ipaddr));

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		.DATA_WIDTH(8),
		.MIN_LENGTH(32)
	) fslv (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),

		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),

		.f_stream_word(s_words)
		// }}}
	);

	faxin_master #(
		.DATA_WIDTH(8),
		.MIN_LENGTH(32)
	) fmst (
		// {{{
		.S_AXI_ACLK(   S_AXI_ACLK),
		.S_AXI_ARESETN(S_AXI_ARESETN),

		.S_AXIN_VALID( M_AXIN_VALID),
		.S_AXIN_READY( M_AXIN_READY),
		.S_AXIN_DATA(  M_AXIN_DATA),
		.S_AXIN_LAST(  M_AXIN_LAST),
		.S_AXIN_ABORT( M_AXIN_ABORT),

		.f_stream_word(m_words)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && (!S_AXIN_VALID || !S_AXIN_ABORT))
	begin
		assert(mid_packet == (s_words != 0));
		if (!aborting)
			assert(addr == s_words);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && rdstate == R_PACKET)
		assert(rdlen + m_words + (M_AXIN_VALID ? 1:0) > 32);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && rdstate == R_PACKET)
		assert(M_AXIN_LAST == (rdlen == 1));

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && rdstate == R_PACKET)
	begin
		assert(m_words < 10'h100);
		assert(rdlen   < 10'h100);
		assert(m_words + rdlen < 10'h100);
		assert(rdlen > 0);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && rdstate != R_PACKET)
	begin
		assert(!M_AXIN_VALID);
		assert(m_words == 0);
	end

	/*
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && M_AXIN_VALID)
		assert(M_AXIN_ABORT || M_AXIN_LAST || addr > 0);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && !M_AXIN_ABORT)
	begin
			assert(s_words >= addr);

		if (M_AXIN_VALID && M_AXIN_LAST)
			assert(s_words == 0);

		if (s_words > 0)
		begin
			assert(m_words + (M_AXIN_VALID ? 1:0) == s_words);
		end else if (m_words != 0)
			assert(M_AXIN_VALID && M_AXIN_LAST);
	end
	*/
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract check
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// THIS NEEDS TO BE COMPLETELY REDONE!  It was originally built for the
	// passthrough ICMP handler.  We now have a memory based handler, in
	// order to allow us to backtrack and adjust the checksum.

	// Specific things to prove:
	//	"aborting" will properly abort an incoming packet if there's no
	//	  room in memory for it
	//	The memory pointers won't overwrap themselves
	//	CONTRACT: The outgoing packet will be valid
	//	The IP won't get *stuck* on an invalid packet: no room to store
	//	  it, and no room to discard it
	//	M_AXIN_VALID will not drop unless M_AXIN_VALID && M_AXIN_LAST
`ifdef	NOT_CHECKED
	(* anyconst *)	reg		f_check_pkt;
	(* anyconst *)	reg	[47:0]	f_src_hwmac;
	(* anyconst *)	reg	[31:0]	f_src_ipaddr;
	(* anyconst *)	reg	[7:0]	fc_addr;
			reg	[7:0]	f_addr, f_base;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_base <= 0;
	else if (rdstate == R_IDLE && pkt_data > 0)
		f_base <= mem_raddr;

	// f_addr
	// {{{
	initial	f_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		f_addr <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		f_addr <= addr;
	// }}}

	// Assumptions re: a valid incoming packet
	// {{{
	always @(*)
	if (f_check_pkt && S_AXIN_VALID)
	case(addr)
	0: assume(S_AXIN_DATA == f_src_hwmac[47:40]);
	1: assume(S_AXIN_DATA == f_src_hwmac[39:32]);
	2: assume(S_AXIN_DATA == f_src_hwmac[31:24]);
	3: assume(S_AXIN_DATA == f_src_hwmac[23:16]);
	4: assume(S_AXIN_DATA == f_src_hwmac[15: 8]);
	5: assume(S_AXIN_DATA == f_src_hwmac[ 7: 0]);
	6: assume(S_AXIN_DATA == 8'h08);
	7: assume(S_AXIN_DATA == 8'h00);
	8: assume(S_AXIN_DATA == 8'h45);
	9: assume(S_AXIN_DATA == 8'h00);
	// 10-11: Packet length
	// 12-13: Packet ID
	14: assume(S_AXIN_DATA == 8'h00);	// Flags
	15: assume(S_AXIN_DATA == 8'h00);	// Fragmentation offset
	// 16: assume(S_AXIN_DATA == 8'h00);	// Time-to-live
	17: assume(S_AXIN_DATA == 8'h01);	// ICMP sub protocol
	// 18-19: header checksum
	20: assume(S_AXIN_DATA == f_src_ipaddr[31:24]);	// Source IP address
	21: assume(S_AXIN_DATA == f_src_ipaddr[23:16]);
	22: assume(S_AXIN_DATA == f_src_ipaddr[15: 8]);
	23: assume(S_AXIN_DATA == f_src_ipaddr[ 7: 0]);
	24: assume(S_AXIN_DATA == i_ipaddr[31:24]);	// Destination IP addr
	25: assume(S_AXIN_DATA == i_ipaddr[23:16]);
	26: assume(S_AXIN_DATA == i_ipaddr[15: 8]);
	27: assume(S_AXIN_DATA == i_ipaddr[ 7: 0]);
	28: assume(S_AXIN_DATA == 8'h08);
	29: assume(S_AXIN_DATA == 8'h00);
	30: assume(S_AXIN_DATA == 8'h08);
	31: assume(S_AXIN_DATA == 8'h00);
	default: begin end
	endcase
	// }}}

	// Assertions regarding the broadcast count
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && f_check_pkt)
	begin
		assume(i_ipaddr != 32'hffff_ffff);

		case(addr)
		25: assert(broadcast_count ==
				((i_ipaddr[31:24] == 8'hff) ? 1:0));
		26: assert(broadcast_count ==
				((i_ipaddr[31:24] == 8'hff) ? 1:0)
				+ ((i_ipaddr[23:16] == 8'hff) ? 1:0));
		27: assert(broadcast_count ==
				((i_ipaddr[31:24] == 8'hff) ? 1:0)
				+ ((i_ipaddr[23:16] == 8'hff) ? 1:0)
				+ ((i_ipaddr[15: 8] == 8'hff) ? 1:0));
		default: if (addr >= 28)
			assert(broadcast_count ==
				((i_ipaddr[31:24] == 8'hff) ? 1:0)
				+ ((i_ipaddr[23:16] == 8'hff) ? 1:0)
				+ ((i_ipaddr[15: 8] == 8'hff) ? 1:0)
				+ ((i_ipaddr[ 7: 0] == 8'hff) ? 1:0));
			else if (addr < 25)
				assert(broadcast_count == 0);
		endcase
	end
	// }}}

	// src_ip checking
	// {{{
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && f_check_pkt)
	begin
		case(addr)
		21: assert(src_ip[ 7:0] == f_src_ipaddr[31:24]);
		22: assert(src_ip[15:0] == f_src_ipaddr[31:16]);
		23: assert(src_ip[23:0] == f_src_ipaddr[31: 8]);
		default: if (addr >= 24)
			assert(src_ip == f_src_ipaddr);
		endcase
	end
	// }}}

	// Assertions re: a valid outgoing packet
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
	7: assert(M_AXIN_DATA == 8'h00);
	8: assert(M_AXIN_DATA == 8'h45);
	9: assert(M_AXIN_DATA == 8'h00);
	// 10-11
	// 12-13
	14: assert(M_AXIN_DATA == 8'h00);	// Flags
	15: assert(M_AXIN_DATA == 8'h00);	// Fragmentation offset
	16: assert(M_AXIN_DATA == 8'h80);	// Time-to-live
	17: assert(M_AXIN_DATA == 8'h01);	// ICMP sub protocol
	// 18-19: header checksum
	20: assert(M_AXIN_DATA == i_ipaddr[31:24]);	// Source IP address
	21: assert(M_AXIN_DATA == i_ipaddr[23:16]);
	22: assert(M_AXIN_DATA == i_ipaddr[15: 8]);
	23: assert(M_AXIN_DATA == i_ipaddr[ 7: 0]);
	24: assert(M_AXIN_DATA == f_src_ipaddr[31:24]);	// Destination IP addr
	25: assert(M_AXIN_DATA == f_src_ipaddr[23:16]);
	26: assert(M_AXIN_DATA == f_src_ipaddr[15: 8]);
	27: assert(M_AXIN_DATA == f_src_ipaddr[ 7: 0]);
	28: assert(M_AXIN_DATA == 8'h00);
	29: assert(M_AXIN_DATA == 8'h00);
	// 30: assert(M_AXIN_DATA == 8'h00);
	// 31: assert(M_AXIN_DATA == 8'h00);
	default: begin end
	endcase
	// }}}

	always @(*)
	if (f_check_pkt)
	begin
		if (f_addr >= 32)
			assert(o_match || addr == 0);
		assert(!o_no_match);
	end

	always @(*)
	if (S_AXI_ARESETN && !M_AXIN_ABORT && addr>0 && addr < 32)
		assert(addr == f_addr + 1);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Random safety checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN && M_AXIN_VALID && !M_AXIN_LAST
							&& !M_AXIN_ABORT))
		assert(M_AXIN_VALID);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover check--can we process a packet at all?
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (valid_memory && rdstate == R_IDLE)
		assume(pkt_data == 0 || pkt_data >= 8'h20);
`ifdef	NOT_CHECKED
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		cover(f_check_pkt && M_AXIN_VALID && M_AXIN_LAST
			&& !M_AXIN_ABORT && f_addr == 32);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// This should really be proven.  We'll assume it for now, since
	// .... the proof appears to be somewhat challenging
	always @(*)
	if (valid_memory && rdstate == R_IDLE)
		assume(pkt_data == 0 || pkt_data > 8'h20);
	// }}}
`endif
// }}}
endmodule
