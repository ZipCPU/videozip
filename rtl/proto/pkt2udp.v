////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/pkt2udp.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Convert an incoming packet of some raw format into UDP format.
//
//	The Ethernet and IP header are provided by a separate AXI stream
//	containing a header.
//
//	This IP is limited to packets that are a multiple of 4 bytes long.
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
`timescale 1ns/1ns
`default_nettype none
// }}}
module	pkt2udp #(
		// {{{
		parameter	LGMEM = 10		// 4kB packet memory
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		// Incoming non-UDP packet
		// {{{
		input	wire		S_AXIN_VALID,
		output	reg		S_AXIN_READY,
		input	wire	[31:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		// }}}
		// Header information to be added to this packet when requested
		// {{{
		input	wire		S_HDR_VALID,
		output	reg		S_HDR_READY,
		input	wire	[31:0]	S_HDR_DATA,
		input	wire		S_HDR_LAST,

		input	wire	[15:0]	i_udp_sport, i_udp_dport,
		// }}}
		// Outgoing UDP packet
		// {{{
		output	reg		M_AXIS_VALID,
		input	wire		M_AXIS_READY,
		output	reg	[31:0]	M_AXIS_DATA,
		output	reg		M_AXIS_LAST,
		// }}}
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[3:0]	S_IDLE     = 0,
				S_HEADER   = 1,
				S_UDP0     = 2,
				S_UDP1     = 3,
				S_PAYLOAD  = 4,
				S_IPLEN    = 5,
				S_IPCKSUM  = 6,
				S_UDPCKSUM = 7,
				S_PKTLEN   = 8;
	localparam	[0:0]	R_IDLE = 0, R_PACKET = 1;

	// localparam [7:0]	UDP_PROTO = 8'd17;
	localparam	ETH_LENW  = 2;
	localparam	IPv4_LENW = 5;
	localparam	UDP_LENW  = 2;
	// localparam	ETH_IPv4_LENW = ETH_LENW + IPv4_LENW;
	localparam	HDR_LENW  = IPv4_LENW + UDP_LENW;
	// Minimum packet size = headers plus the size word
	localparam	MIN_PACKET_SIZE = ETH_LENW + IPv4_LENW + UDP_LENW + 1;

	reg	[3:0]	state;
	reg		rdstate, abort_header, abort_packet;

	reg	[32:0]	ip_checksum, udp_checksum;
	reg	[13:0]	ip_length, payload_length;
	wire	[15:0]	udp_length;
	reg	[3:0]	hdrpos;

	reg			mem_wr, m_lenword;
	reg	[31:0]		mem_wdata, pkt_data, rdlen, pktlen;
	reg	[LGMEM-1:0]	mem_waddr, mem_raddr;
	wire	[LGMEM-1:0]	w_mem_raddr;
	reg	[LGMEM-1:0]	start_of_packet, next_start_of_packet,
				end_of_write_packet;
	reg	[31:0]		mem	[0:(1<<LGMEM)-1];
	reg	[15:0]		proto_word;

	wire	[LGMEM-1:0]	space_in_use, space_limit;// space_available;
	reg		void_read;
	reg	[1:0]	void_pipe;


	assign	udp_length={ payload_length, 2'b00 }+{ UDP_LENW[13:0], 2'b00 };

	wire	start_new_write;
	wire	start_run;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Pre-write cycle
	// {{{
	assign	start_new_write = S_AXIN_VALID && !abort_header
			&& (space_in_use + MIN_PACKET_SIZE < (1<<LGMEM)-1);
	always @(posedge S_AXI_ACLK)
	begin
		case(state)
		S_IDLE:	 begin
			// {{{
			mem_wr    <= 1'b1;
			mem_waddr <= next_start_of_packet;
			start_of_packet <= next_start_of_packet;
			end_of_write_packet   <= next_start_of_packet;
			payload_length <= 0;
			mem_wdata <= 0;
			hdrpos    <= 0;
			ip_length    <= -2;	// Minus two words for ETH
			ip_checksum  <= 0;
			udp_checksum <= 0;

			if (S_AXIN_VALID && !abort_header
					&& (space_in_use + MIN_PACKET_SIZE < (1<<LGMEM)-1))
			begin
				state <= S_HEADER;
				end_of_write_packet <= next_start_of_packet + MIN_PACKET_SIZE;
			end end
			// }}}
		S_HEADER: begin
			// {{{
			mem_wr    <= 1'b0;
			mem_wdata <= S_HDR_DATA;
			payload_length <= 0;
			if (S_HDR_VALID && S_HDR_READY)
			begin
				mem_wr    <= 1'b1;
				ip_length <= ip_length + 1;
				mem_waddr <= mem_waddr + 1;
				hdrpos    <= hdrpos + 1;

				if (hdrpos == 4)
					proto_word <= S_HDR_DATA[31:16];

				// Start calculating the checksum over the pseudo-header
				if (hdrpos >= ETH_LENW)
					ip_checksum  <= ip_checksum[31:0]
						+ S_HDR_DATA
						+ (ip_checksum[32] ? 33'h1:0);
				case(hdrpos)
				// No length yet
				// 2 = ETH_LENW = start of IP header
				// ETH_LENW: udp_checksum <= udp_checksum[31:0]
				//	+ { 16'h0, S_HDR_DATA[15:0] }
				//	+ (udp_checksum[32] ? 33'h1 : 0);
				// 3 = Packet ID and Fragmentation info
				//
				// 4: This will get filled in later, but we can
				// include the protocol for now
				4: udp_checksum <= udp_checksum[31:0]
					+ { 8'h0, 8'h11, 16'h0 }
					+ (udp_checksum[32] ? 33'h1 : 0);
				// Source address
				5: udp_checksum <= udp_checksum[31:0]
					+ S_HDR_DATA[31:0]
					+ (udp_checksum[32] ? 33'h1 : 0);
				// Destination address
				6: udp_checksum <= udp_checksum[31:0]
					+ S_HDR_DATA[31:0]
					+ (udp_checksum[32] ? 33'h1 : 0);
				default: begin end
				endcase

				if (S_HDR_LAST)
					state <= S_UDP0;
			end end
			// }}}
		S_UDP0: begin
			// {{{
			ip_length <= ip_length + 1;

			mem_wr <= 1'b1;
			mem_wdata <= { i_udp_sport, i_udp_dport };
			mem_waddr <= mem_waddr + 1;
			payload_length <= 0;
			ip_checksum <= { 16'h0, ip_checksum[15:0] }
				+ { 16'h0, ip_checksum[31:16] }
				+ (ip_checksum[32] ? 33'h1 : 0);
			udp_checksum <= udp_checksum[31:0]
				+ { i_udp_sport, i_udp_dport }
				+ (udp_checksum[32] ? 33'h1 : 0);

			state <= S_UDP1;
			end
			// }}}
		S_UDP1: begin
			// {{{
			ip_length <= ip_length + 1;
			ip_checksum <= { 16'h0, ip_checksum[15:0] }
				+ { 16'h0, ip_checksum[31:16] }
				+ (ip_checksum[32] ? 33'h1 : 0);

			// We'll have to come back and fill this in later, since
			// we don't (yet) know either the full length or the
			// UDP checksum
			mem_wr <= 1'b1;
			mem_wdata <= 32'h00; // Should be 16'b length, 16'bcksum
			mem_waddr <= mem_waddr + 1;
			payload_length <= 0;

			state <= S_PAYLOAD;
			end
			// }}}
		S_PAYLOAD: begin
			// {{{
			mem_wr    <= S_AXIN_VALID && S_AXIN_READY;
			mem_wdata <= S_AXIN_DATA;
			end_of_write_packet   <= mem_waddr + 1;
			if (S_AXIN_VALID && S_AXIN_READY)
			begin
				ip_length <= ip_length + 1;

				mem_waddr <= mem_waddr + 1;
				end_of_write_packet   <= mem_waddr + 2;
				payload_length <= payload_length + 1;
				udp_checksum <= udp_checksum[31:0]
						+ S_AXIN_DATA
						+(udp_checksum[32] ? 33'h1 : 0);
				if (S_AXIN_LAST)
					state <= S_IPLEN;
			end end
			// }}}
		S_IPLEN: begin
			// {{{
			mem_wr <= 1'b1;
			mem_wdata <= { 8'h45, 8'h00, ip_length, 2'b00 };
			mem_waddr <= start_of_packet + ETH_LENW + 1;
			udp_checksum <= { 16'h0, udp_checksum[15:0] }
					+ { 16'h0, udp_checksum[31:16] }
					+ { 15'h0, udp_length[15:0], 1'b0 }
					+(udp_checksum[32] ? 33'h1 : 0);
			ip_checksum <= ip_checksum+ { 16'h0, ip_length, 2'b00 };

			state <= S_IPCKSUM;
			end
			// }}}
		S_IPCKSUM: begin
			// {{{
			mem_wr <= 1'b1;
			mem_wdata[31:16]<= proto_word;
			mem_wdata[15:0] <= ~(ip_checksum[15:0]
					+ (ip_checksum[16] ? 16'h1 : 0));
			mem_waddr <= start_of_packet + ETH_LENW + 3;

			udp_checksum <= { 16'h0, udp_checksum[15:0] }
					+ { 16'h0, udp_checksum[31:16] }
					+ (udp_checksum[32] ? 33'h1 : 0);

			state <= S_UDPCKSUM;
			end
			// }}}
		S_UDPCKSUM: begin
			// {{{
			mem_wr <= 1'b1;
			mem_wdata <= { udp_length, ~udp_checksum[15:0] };
			mem_waddr <= start_of_packet + ETH_LENW + IPv4_LENW + 2;

			state <= S_PKTLEN;
			end
			// }}}
		S_PKTLEN: begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr <= start_of_packet;

			// Verilator lint_off WIDTH
			// Record the packet length in bytes
			mem_wdata <= (ETH_LENW + HDR_LENW+payload_length+1)<<2;
			next_start_of_packet <= end_of_write_packet;
// start_of_packet + payload_length + ETH_LENW + HDR_LENW + 1;
			// Verilator lint_on WIDTH
			state <= S_IDLE;
			end
			// }}}
		default: begin end
		endcase

		if ((S_AXIN_ABORT && state <= S_PAYLOAD) || abort_packet)
		begin
			// {{{
			mem_wr <= 1'b1;
			mem_waddr     <= next_start_of_packet;
			end_of_write_packet <= next_start_of_packet;
			mem_wdata <= 0;

			if (state == S_HEADER)
				abort_header <= 1'b1;

			state <= S_IDLE;
			// }}}
		end

		if (abort_header && S_HDR_VALID && S_HDR_LAST)
			abort_header <= 1'b0;

		if (!S_AXI_ARESETN)
		begin
			// {{{
			mem_wr    <= 1'b0;
			mem_waddr <= 0;
			state <= S_IDLE;
			abort_header <= 1'b0;
			start_of_packet <= 0;
			next_start_of_packet <= 0;
			end_of_write_packet <= 0;
			// }}}
		end
	end
	// }}}

	// assign	space_available = mem_raddr - next_start_of_packet;
	assign	space_in_use = end_of_write_packet - mem_raddr;
	assign	space_limit  = (1<<LGMEM) - 1;

	// S_HDR_READY
	// {{{
	// assign	S_HDR_READY  = (state == S_HEADER) || abort_header;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_HDR_READY <= 1'b0;
	else begin
		if (!S_AXIN_ABORT && state == S_IDLE
				&& !abort_packet &&
				start_new_write)
			S_HDR_READY <= 1'b1;

		if (S_HDR_VALID && S_HDR_READY && S_HDR_LAST)
			S_HDR_READY <= 1'b0;
		else if (abort_header)
			S_HDR_READY <= 1'b1;
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN & !abort_header)
	begin
		assert(S_HDR_READY == (state == S_HEADER));
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN & $past(S_AXI_ARESETN) && $past(abort_header))
	begin
		if (abort_header)
			assert(S_HDR_READY);
		if ($past(S_HDR_VALID && S_HDR_READY && S_HDR_LAST))
			assert(!S_HDR_READY);
		else
			assert(S_HDR_READY);
	end
`endif
	// }}}

	// S_AXIN_READY
	// {{{
	// assign	S_AXIN_READY = S_AXIN_ABORT || abort_packet ||
	//	((state == S_PAYLOAD) && (space_in_use < space_limit));

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXIN_READY <= 1'b0;
	else begin
		// if (state == S_UDP1 && !abort_header)
		//	S_AXIN_READY <= 1'b1;

		if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
			S_AXIN_READY <= 1'b0;
		else if (state == S_PAYLOAD || state == S_UDP1)
			S_AXIN_READY <= (space_in_use
				+ (S_AXIN_VALID && S_AXIN_READY ? 1:0)
				< space_limit);

		if (S_AXIN_ABORT)
			S_AXIN_READY <= (!S_AXIN_READY && S_AXIN_VALID);
		else if (abort_packet)
			S_AXIN_READY <= !(S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST);
	end
`ifdef	FORMAL
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (!S_AXIN_ABORT && !abort_packet && (state != S_PAYLOAD))
			assert(!S_AXIN_READY);

		if ($past(abort_packet) && abort_packet)
			assert(S_AXIN_READY);
		if (state == S_PAYLOAD && space_in_use == space_limit)
			assert(!S_AXIN_READY);
		else if (state == S_PAYLOAD
				&& ($past(space_in_use + 1 < space_limit)))
			assert(S_AXIN_READY);
	end
`endif
	// }}}

	// abort_packet
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		abort_packet <= 1'b0;
	else if (S_AXIN_ABORT)
		abort_packet <= 1'b0;
	else if (!abort_packet)
	begin
		if ((start_of_packet == mem_raddr) && (state == S_PAYLOAD)
					&& (space_in_use >= space_limit))
			abort_packet <= 1;
	end else if (abort_packet)
	begin
		if (S_AXIN_ABORT)
			abort_packet <= 0;
		if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
			abort_packet <= 0;
	end
	// }}}

	// Write to memory
	// {{{
	always @(posedge S_AXI_ACLK)
	if (mem_wr)
		mem[mem_waddr[LGMEM-1:0]] <= mem_wdata;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read the packet back out from memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// void_ready, void_pipe
	// {{{
	// Give the memory writer a chance to clear the first value of memory
	// before we try to read it, otherwise we might read an invalid
	// length and start transmitting a packet that ... isn't.
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		{ void_read, void_pipe } <= -1;
	else if (M_AXIS_VALID)
		{ void_read, void_pipe } <= -1;
	else
		{ void_read, void_pipe } <= { void_pipe, 1'b0 };
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	case({ void_read, void_pipe })
	2'b11: begin end
	2'b10: begin end
	2'b00: begin end
	2'b01: assert(0);
	endcase
`endif
	// }}}

	// mem_raddr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mem_raddr <= 0;
	else if (m_lenword || (M_AXIS_VALID && M_AXIS_READY && rdlen > 2))
		mem_raddr <= mem_raddr + 1;
	else if (start_run)
		mem_raddr <= mem_raddr + 2;
	// }}}

	// pkt_data
	// {{{
	assign	w_mem_raddr = mem_raddr + (start_run ? 1:0);

	always @(posedge S_AXI_ACLK)
	if (rdstate == R_IDLE || M_AXIS_LAST || m_lenword
					|| (M_AXIS_VALID && M_AXIS_READY))
		pkt_data <= mem[w_mem_raddr];
	// }}}

	// rdstate, rdlen
	// {{{
	assign	start_run = rdstate == R_IDLE && pkt_data > 0 && !void_read;

	always @(*)
	begin
		// How many words are in a packet?
		//
		// Round up to the nearest larger word.  This would actually be
		// useful if our packets might have a length other than an
		// even number of words.
		// pktlen = pkt_data + 3;
		pktlen = pkt_data >> 2;
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		rdstate <= R_IDLE;
		rdlen   <= 0;
	end else if (m_lenword)
	begin
		rdlen <= rdlen - 1;
	end else if (M_AXIS_VALID)
	begin
		if (M_AXIS_READY)
		begin
			if (M_AXIS_LAST)
				rdstate <= R_IDLE;
			rdlen <= rdlen - 1;
		end
	end else if (start_run)
	begin
		rdstate <= R_PACKET;
		rdlen   <= pktlen;
	end

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (rdstate == R_PACKET)
		begin
			assert(!m_lenword || !M_AXIS_VALID);
			assert(m_lenword || M_AXIS_VALID);
			assert(rdlen > 0);
			assert(M_AXIS_LAST == (rdlen == 1));
		end else begin
			assert(!M_AXIS_VALID);
			assert(rdlen == 0);
		end

		assert(rdlen <= (1<<LGMEM)-1);
	end

	//		START	PAYL	LAST
	//	RDLEN	3FF	3F5	1		(Always ready)
	//	DATA		..000	3F4
	//
	//	RDLEN	3FF	3F5	1
	//	DATA		0000	3F4
`endif
	// }}}

	// m_lenword
	// {{{
	initial	m_lenword = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_lenword <= 0;
	else if (M_AXIS_VALID || m_lenword)
		m_lenword <= 1'b0;
	else
		m_lenword <= start_run;
	// }}}

	// M_AXIS_VALID
	// {{{
	initial	M_AXIS_VALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_VALID <= 0;
	else if (!M_AXIS_VALID)
		M_AXIS_VALID <= m_lenword;
	else if (M_AXIS_READY && M_AXIS_LAST)
		M_AXIS_VALID <= 1'b0;
	// }}}

	// M_AXIS_LAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_LAST <= 0;
	else if (M_AXIS_VALID && M_AXIS_READY)
	begin
		if (M_AXIS_LAST)
			M_AXIS_LAST <= 0;
		else
			M_AXIS_LAST <= (rdlen <= 2);
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && !M_AXIS_VALID)
		assert(!M_AXIS_LAST);
`endif
	// }}}

	// M_AXIS_DATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIS_DATA <= 0;
	else if (!M_AXIS_VALID || M_AXIS_READY)
		M_AXIS_DATA <= pkt_data;
	// }}}

	// assign	o_debug = { rdstate, state };
	always @(posedge S_AXI_ACLK)
	begin
		o_debug <= { 1'b0,
			rdstate,					// 1b
			state,						// 4b
			S_AXIN_VALID, S_AXIN_READY, S_AXIN_LAST, S_AXIN_ABORT,	// 4b
			M_AXIS_VALID, M_AXIS_READY,			// 2b
			{(10-LGMEM){1'b0}}, mem_waddr, {(10-LGMEM){1'b0}}, mem_raddr				// 20b
			};
		if (M_AXIS_VALID && M_AXIS_READY)
			o_debug[19:0] <= M_AXIS_DATA[19:0];
		else if (rdstate == R_IDLE && pkt_data > 0 && !void_read)
			o_debug[19:0] <= pkt_data[19:0];
	end

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
	localparam	F_MIN_PAYLOAD = 2;
	localparam	F_MIN_PACKET  = MIN_PACKET_SIZE + F_MIN_PAYLOAD;
	localparam	F_HDRSZ = 7;


	reg	f_past_valid;
	wire	[10:0]	slv_words;
	wire	[11:0]	slv_packets;
	wire	[3:0]	hdr_words;
	wire	[11:0]	hdr_packets;
	reg	[LGMEM-1:0]	f_header_addr, f_payload_addr,
				f_end_of_header;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	////////////////////////////////////////////////////////////////////////
	//
	// Abortable AXI-packet stream (input) properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	faxin_slave #(
		.DATA_WIDTH(32),
		.MIN_LENGTH(F_MIN_PAYLOAD)
	) fslave (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(S_AXIN_VALID),
		.S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA),
		.S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		//
		.f_stream_word(slv_words),
		.f_packets_rcvd(slv_packets)
		// }}}
	);

	// AXI header properties
	faxin_slave #(
		// {{{
		.DATA_WIDTH(32),
		.MIN_LENGTH(F_HDRSZ),
		.MAX_LENGTH(F_HDRSZ)
		// }}}
	) fheader (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(S_HDR_VALID),
		.S_AXIN_READY(S_HDR_READY),
		.S_AXIN_DATA(S_HDR_DATA),
		.S_AXIN_LAST(S_HDR_LAST),
		.S_AXIN_ABORT(1'b0),
		//
		.f_stream_word(hdr_words),
		.f_packets_rcvd(hdr_packets)
		// }}}
	);

	always @(*)
	if (S_HDR_VALID && hdr_words == 1)
		assume(S_HDR_DATA[15:0] == 16'h0800);

	always @(*)
	if (S_HDR_VALID && hdr_words == 2)
	begin
		assume(S_HDR_DATA[31:24] == 8'h45);
		assume(S_HDR_DATA[15: 0] == 16'h00);
	end

	always @(*)
	if (S_HDR_VALID && hdr_words == 3)
		assume(S_HDR_DATA[19:0] == 20'h00000);

	always @(*)
	if (S_AXI_ARESETN && hdr_words != 0 && !abort_header)
	begin
		assert(state == S_HEADER);
	end

	always @(*)
		f_header_addr = start_of_packet + hdr_words;

	always @(*)
	if (S_AXI_ARESETN)
	case(state)
	S_IDLE:		begin assert(abort_packet || slv_words == 0); end
	S_HEADER:	begin assert(slv_words == 0); assert(hdrpos == hdr_words); assert(!abort_header); end
	S_UDP0:		begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_UDP1:		begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_PAYLOAD:	begin assert(payload_length == slv_words); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_IPLEN:	begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_IPCKSUM:	begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_UDPCKSUM:	begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	S_PKTLEN:	begin assert(slv_words == 0); assert(hdrpos == F_HDRSZ); assert(!abort_header); end
	default: assert(0);
	endcase

	assign	f_end_of_header = start_of_packet + MIN_PACKET_SIZE;

	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE && state < S_PAYLOAD)
	begin
		assert(S_AXIN_VALID);
		assert(space_in_use < (1<<LGMEM));
		assert(end_of_write_packet == f_end_of_header);
	end

	always @(*)
	if (S_AXI_ARESETN && !abort_header && hdr_words != 0)
	begin
		assert(state == S_HEADER);
	end

	always @(*)
	if (S_AXI_ARESETN && state == S_HEADER)
	begin
		assert(!abort_header);
		assert(mem_waddr == f_header_addr);
		assert(hdrpos == hdr_words);
	end

	// Verify payload_length && mem_waddr for state >= S_PAYLOAD
	// {{{
	always @(*)
		f_payload_addr = start_of_packet + F_HDRSZ + UDP_LENW
				+ payload_length;
	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
		assert(payload_length + F_HDRSZ + UDP_LENW <= (1<<LGMEM)-1);

	always @(*)
	if (S_AXI_ARESETN && !abort_packet && state == S_PAYLOAD)
		assert(mem_waddr == f_payload_addr);

	always @(*)
	if (S_AXI_ARESETN && !abort_packet && state >= S_PAYLOAD)
	begin
		if (end_of_write_packet == 0)
		begin
			assert(&f_payload_addr);
		end else begin
			assert(end_of_write_packet == f_payload_addr + 1);
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Outoing) AXI-stream properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!M_AXIS_VALID);
	else if ($past(M_AXIS_VALID && !M_AXIS_READY))
	begin
		assert(M_AXIS_VALID);
		assert($stable(M_AXIS_DATA));
		assert($stable(M_AXIS_LAST));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction requirement(s)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Properties:
	// - Packet lengths must be between (1+2+5+2=) 10 and (memsize - 1) wrds
	// - RDPTR <= RDNXT <= StartofPkt <= WPTR <= MEMSZ-1
	//  DNXTRD  = RDNXT -RDPTR
	//  DSTRTRD = STRTPkt-RDPTR
	//  DWRTRD  = WPTR-RDPTR

	// The read pointer can never be allowed to overflow
	wire	[LGMEM-1:0]	end_of_packet_addr, readable_data;
	reg			f_rdstate;
	(* anyconst *) reg [LGMEM-1:0]	fc_rdfirst, fc_rdsecond;
	reg	[LGMEM-1:0]	f_rdbase, f_rdnext, fc_distance,
				f_rdfirst_plus, f_rdbase_plus;
	reg	[LGMEM-1:0]	f_write_to_read, f_start_to_read,
				f_next_to_read, f_end_to_read, fc_to_read,
				f_base_to_first, f_base_to_second,
				fcfirst_to_read, fw_next_end,
				fw_next_to_read, f_read_to_base,
				f_start_to_first, f_start_to_second;
	reg	[31:0]	mem_at_raddr, f_rdlen;
	reg	[31:0]	mem_at_rdfirst, mem_at_rdsecond;

	// f_rdbase, f_rdlen, f_rdnext -- current read pointers
	// {{{
	always @(*)
		mem_at_raddr = mem[mem_raddr];

	always @(*)
		fw_next_end = mem_raddr + mem_at_raddr[LGMEM+1:2]
				+ ((mem_at_raddr[1:0] != 0) ? 1:0);

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		f_rdbase <= 0;
		f_rdlen  <= 0;
		f_rdnext <= 0;
	end else if (start_run)
	begin
		f_rdbase <= mem_raddr;
		f_rdlen  <= mem_at_raddr;
		f_rdnext <= fw_next_end;
	end else if (rdstate == R_IDLE)
	begin
		f_rdbase <= mem_raddr;
		f_rdlen  <= 0;
		f_rdnext <= mem_raddr;
	end else if (M_AXIS_VALID && M_AXIS_READY && M_AXIS_LAST)
		f_rdbase <= f_rdnext;

	always @(*)
	if (S_AXI_ARESETN)
		assert((rdstate == R_PACKET) == (f_rdbase != f_rdnext));

	always @(*)
		f_rdbase_plus = f_rdbase + (f_rdlen>>2);

	always @(*)
	if (S_AXI_ARESETN && !start_run && f_rdlen > 0)
		assert((f_rdlen>>2) >= F_MIN_PACKET && (f_rdlen>>2) <= (1<<LGMEM)-1);

	always @(*)
	if (S_AXI_ARESETN && f_rdbase != f_rdnext)
		assert(f_rdbase_plus == f_rdnext);
	// }}}

	always @(*)
	if (S_AXI_ARESETN && rdstate != R_IDLE)
	begin
		if (M_AXIS_LAST)
		begin
			assert(f_rdnext == mem_raddr);
		end else
			assert(f_rdnext == end_of_packet_addr);
	end

	always @(*)
	if (S_AXI_ARESETN && rdstate == R_IDLE)
		assert(f_rdbase == mem_raddr);

	always @(*)
	if (S_AXI_ARESETN && rdstate == R_IDLE && !start_run)
		assert((mem[mem_raddr] >= (F_MIN_PACKET << 2))
			||(start_of_packet == mem_raddr));

	// f_rdstate, f_rdfirst, f_rdsecond -- saved/tracked pointers
	// {{{
	initial	f_rdstate <= 1'b0;
	always @(posedge S_AXI_ACLK)
	begin
		if (f_rdstate == 0 && state == S_PKTLEN)
		begin
			// f_rdfirst  <= start_of_packet;
			// f_rdsecond <= end_of_packet;
			if ((fc_rdfirst == start_of_packet)
				&&(fc_rdsecond == end_of_write_packet)) // ACTIVE!
				f_rdstate <= 1'b1;
		end else if (start_run && mem_raddr == fc_rdfirst)
			f_rdstate <= 1'b0;

		if (!S_AXI_ARESETN)
		begin
			f_rdstate  <= 1'b0;
			// fc_rdfirst  <= 0;
			// fc_rdsecond <= 0;
		end
	end

	assign	fc_distance = fc_rdsecond - fc_rdfirst;
	assign	fc_to_read  = fc_rdsecond - mem_raddr;

	always @(*)
		assume(fc_distance >= F_MIN_PACKET);
	// }}}

	always @(*)
		mem_at_rdfirst = mem[fc_rdfirst];

	always @(*)
		mem_at_rdsecond  = mem[fc_rdsecond];

	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE && fc_rdfirst == start_of_packet)
	begin
		if (mem_at_rdfirst != 0)
		begin
			assert(state  == S_HEADER || state == S_IDLE);
			assert(hdrpos == 0);
			assert(mem_wr);
			assert(mem_wdata == 0);
			assert(mem_waddr == fc_rdfirst);
		end else begin
			assert(mem_at_rdfirst == 0);
		end
	end

	always @(*)
	if (S_AXI_ARESETN)
	begin
		if (f_rdstate)
		begin
			assert(f_next_to_read <= fcfirst_to_read);

			if (mem_at_rdfirst == 0)
			begin
				assert(state == S_IDLE);
				assert(mem_wr);
				assert(mem_waddr == fc_rdfirst);
				assert(mem_wdata > 0);
				assert(start_of_packet != next_start_of_packet);
				assert(start_of_packet == mem_waddr);
				assert(start_of_packet == fc_rdfirst);
			end else begin
				assert(f_start_to_read >= fc_to_read);
				assert(next_start_of_packet != fc_rdfirst);
				assert(f_start_to_first == fc_distance
					|| f_start_to_first >= fc_distance + F_MIN_PACKET);
				assert(mem_at_rdfirst[1:0] == 2'b0);
				assert(mem_at_rdfirst[31:2] >= F_MIN_PACKET);
				assert(mem_at_rdfirst[31:2] <= (1<<LGMEM)-1);
				assert(mem_at_rdfirst[31:2] == fc_distance);
			end

			// if (!mem_wr || mem_waddr != fc_rdsecond)
			// begin
				assert(fc_to_read >= fc_distance);
				assert(f_end_to_read >= fc_to_read);
				assert(fcfirst_to_read >= f_next_to_read);
				assert(fcfirst_to_read <= f_start_to_read);
			// end

			if (mem_wr && mem_waddr == fc_rdsecond)
			begin
				if (mem_wdata == 0)
				begin
					assert(state == S_IDLE || state == S_HEADER);
				end else begin
					assert(state == S_IDLE);
					assert(start_of_packet == fc_rdsecond);
					assert(start_of_packet != next_start_of_packet);
				end
			end else if (start_of_packet == next_start_of_packet)
			begin
				assert(mem_at_rdsecond[1:0] == 2'b0);
				if (mem_at_rdsecond == 0)
				begin
					assert(start_of_packet == fc_rdsecond);
				end else begin
					assert(mem_at_rdsecond[31:2] >= F_MIN_PACKET);
					assert(fc_distance == mem_at_rdfirst[31:2]);
				end
				assert(mem_at_rdsecond[31:2] <= (1<<LGMEM)-1);
			end
		end

		if (f_rdstate && (mem_raddr == fc_rdfirst || mem_raddr == fc_rdsecond))
		begin end else if(rdstate == R_IDLE)
		begin
			assume(mem_at_raddr[1:0] == 2'b0);
			if (mem_raddr == start_of_packet)
			begin
				assume(mem_at_raddr == 0);
			end else begin
				assume(f_start_to_read > fw_next_to_read);
				assume(f_start_to_read - fw_next_to_read >= F_MIN_PACKET);
				assume(fcfirst_to_read >= fw_next_to_read);
				assume(mem_at_raddr[31:2] >= F_MIN_PACKET);
				assume(mem_at_raddr[31:2] <= (1<<LGMEM)-1);
				// if (f_rdstate)
				//	assume(mem_at_raddr + mem_raddr == fc_rdfirst)
				//		|| (fc_rdfirst - (mem_at_raddr +mem_raddr) >= F_MIN_PACKET)
			end
		end
	end

	always @(*)
	if (S_AXI_ARESETN && f_rdstate)
		assert(fc_distance >= F_MIN_PACKET && fc_distance <= (1<<LGMEM)-1);

	always @(*)
		f_rdfirst_plus = fc_rdfirst + (mem_at_rdfirst >> 2);

	assign	readable_data = start_of_packet - mem_raddr;

	assign	end_of_packet_addr = (rdstate == R_IDLE) ? mem_raddr
					: (mem_raddr + rdlen -2);
	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		assert(!rdstate || readable_data + 2 >= rdlen);

		if (start_of_packet == fc_rdfirst)
		begin
			if (mem_at_rdfirst != 0)
			begin
				assert(state == S_IDLE || state == S_HEADER);
				assert(mem_wr);
				assert(mem_waddr == fc_rdfirst);
				assert(mem_wdata == 0);
			end
		end

		if (start_of_packet == fc_rdsecond)
		begin
			if (mem_at_rdsecond != 0)
			begin
				assert(state == S_IDLE || state == S_HEADER);
				assert(mem_wr);
				assert(mem_waddr == fc_rdsecond);
				assert(mem_wdata == 0);
			end
		end


		if (mem_waddr != start_of_packet)
		begin
			if (start_of_packet == fc_rdfirst)
			begin
				assert(mem_at_rdfirst == 0);
			end else if (start_of_packet == fc_rdsecond)
			begin
				assert(mem_at_rdsecond == 0);
			end else begin
				assume(mem[start_of_packet] == 0);
			end
		end
	end

	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
		assert(start_of_packet == next_start_of_packet);

	always @(*)
	begin
		f_write_to_read = mem_waddr       - mem_raddr;
		f_start_to_read = start_of_packet - mem_raddr;//== readable_data
		f_next_to_read  = f_rdnext        - mem_raddr;
		fw_next_to_read = fw_next_end     - mem_raddr;
		f_end_to_read   = end_of_write_packet   - mem_raddr;

		f_read_to_base  = mem_raddr - f_rdbase;

		f_base_to_first  = f_rdbase - fc_rdfirst;
		f_base_to_second = f_rdbase - fc_rdsecond;
		f_start_to_first  = start_of_packet - fc_rdfirst;
		f_start_to_second = start_of_packet - fc_rdsecond;

		fcfirst_to_read = fc_rdfirst - mem_raddr;
		// fc_to_read  = f_rdsecond - mem_raddr;
	end

	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(f_next_to_read  <= f_start_to_read);
		assert(f_start_to_read <= f_write_to_read);
		assert(f_write_to_read <= f_end_to_read);
		assert(f_start_to_read <= f_end_to_read);
		assert(f_end_to_read <= (1<<LGMEM)-1);

		// mem_raddr -> f_rdnext cannot overlap
		//	start_of_packet -> end_of_write_packet

		if (rdstate != R_IDLE && f_start_to_read != f_next_to_read)
		begin
			assert(f_start_to_read -f_next_to_read >= F_MIN_PACKET);
			assert(f_start_to_read -f_next_to_read <= (1<<LGMEM)-1);
		end

		if (rdstate != R_IDLE)
			assert(f_read_to_base <= f_rdlen[LGMEM+1:2]);

		//
		// Can't' make this assertion.  Once f_rdnext has been
		// chosen and set, mem_raddr may eat into it.  All I can
		// then say is it must be >= 0, which for unsigned #'s is
		// tautologous.
		//
		// if (rdstate != R_IDLE)
		//	assert(f_next_to_read > F_MIN_PACKET);

		// if (f_rdsecond != f_rdnext)
		// fc_to_read  = f_rdsecond - mem_raddr;
	end

	always @(*)
	if (S_AXI_ARESETN && state > S_PAYLOAD)
	begin
		assert(mem_wr);
		assert(payload_length >= F_MIN_PAYLOAD);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		cover(M_AXIS_VALID && M_AXIS_READY);

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		cover(state == S_PAYLOAD && !S_AXIN_READY); // Step 20, LGMEM=5

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		cover(abort_packet); //	Step 21, for LGMEM=5

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover(state == S_IDLE && $past(state == S_PKTLEN));

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover($fell(abort_header));	// Trace 0?

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover($fell(abort_packet)); //	Step 22, for LGMEM=5

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover(rdstate == R_PACKET);	// Step 22, tra 4

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN))
		cover($fell(rdstate));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyconst *)	reg	[15:0]	fc_udp_sport, fc_udp_dport;

	always @(*)
	if (state != S_IDLE)
	begin
		assume(i_udp_sport == fc_udp_sport);
		assume(i_udp_dport == fc_udp_dport);
	end
	// }}}
`endif
// }}}
endmodule
