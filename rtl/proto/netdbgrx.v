////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/netdbgrx.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	First stage processing of a network debugging packet.  Handles
//		synchronization, repeat detection, and GPIO outputs.
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
module	netdbgrx #(
		parameter [7:0]	GPIO_AUTO_CLEAR = 8'h7,
		parameter [7:0]	DEF_GPIO = 8'h0,
		parameter [0:0]	OPT_REPEAT_SUPPRESSION = 1'b1
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		// Incoming interface
		// {{{
		input	wire		S_AXI_TVALID,
		output	wire		S_AXI_TREADY,
		input	wire [31:0]	S_AXI_TDATA,
		// No S_AXI_TLAST.  Packet size is captured by the first word
		// in the packet
		// }}}
		// Outgoing GPIO registers
		// {{{
		output	reg	[7:0]	o_gpio,
		// }}}
		// Outgoing interface
		// {{{
		output	reg		o_sync, o_repeat_stb, o_null_pkt,
		output	reg	[47:0]	o_host_mac,
		output	reg	[31:0]	o_host_ip,
		output	reg	[15:0]	o_host_udpport,
		output	reg	[15:0]	o_host_frameid,
		//
		input	wire		i_handler_busy,
		// }}}
		// Payload interface
		// {{{
		output	wire		M_AXI_TVALID,
		input	wire		M_AXI_TREADY,
		output	wire	[7:0]	M_AXI_TDATA,
		output	wire		M_AXI_TLAST,
		// }}}
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	reg	[15:0]	pktlen;
	reg	[5:0]	addr;
	reg		nomatch, drop, r_syncd;
	reg		word_valid;
	reg	[31:0]	word_data;
	reg	[3:0]	word_last;

	reg	[47:0]	tmp_mac;
	reg	[31:0]	tmp_ip;
	reg	[15:0]	tmp_sport;

	wire		word_ready;

	reg		m_valid;
	reg	[31:0]	m_data;
	reg	[2:0]	m_loaded;
	reg	[3:0]	m_last;
	wire	[3:0]	new_load;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #1: Process the incoming packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	S_AXI_TREADY = (addr < 10)|| drop ||(!word_valid || word_ready);
	assign	word_ready = (!M_AXI_TVALID ||(M_AXI_TREADY && !m_loaded[2]));

	// addr
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		addr    <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (pktlen > 4 || (addr == 0 && S_AXI_TDATA[15:0] > 4))
		begin
			if (!addr[5])
				addr <= addr + 1;
		end else
			addr <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert((addr == 0) == (pktlen == 0));
`endif
	// }}}

	// pktlen
	// {{{
	initial	pktlen = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pktlen	<= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		if (addr == 0)
			pktlen <= (S_AXI_TDATA[15:0] > 4) ? (S_AXI_TDATA[15:0] - 4) : 0;
		else if (pktlen <= 4)
			pktlen <= 0;
		else
			pktlen <= pktlen - 4;
	end
	// }}}

	// o_null_pkt
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !r_syncd)
		o_null_pkt    <= 0;
	else if (S_AXI_TVALID && S_AXI_TREADY && addr == 10 && !nomatch
				&& r_syncd
				&& S_AXI_TDATA[31:16] != o_host_frameid
				&& S_AXI_TDATA[31:16] != 0)
		o_null_pkt <= (pktlen == 4) && (!i_handler_busy)
				&& !word_valid && !m_valid;
	else
		o_null_pkt <= 1'b0;
	// }}}

	initial	word_last  = 4'b0;
	initial	o_gpio     = DEF_GPIO;
	initial	o_repeat_stb  = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		nomatch <= 0;
		o_gpio  <= DEF_GPIO;
		o_repeat_stb  <= 1'b0;
		// }}}
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		o_gpio <= o_gpio & ~GPIO_AUTO_CLEAR;
		o_repeat_stb <= 0;

		case(addr)
		0: begin // Capture the packet length
			// {{{
			nomatch <= 0;
			drop <= 0;
			end
			// }}}
		1: begin // Match the source MAC address
			// {{{
			if (S_AXI_TDATA != o_host_mac[47:16])
			begin
				tmp_mac[47:16] <= S_AXI_TDATA;
				nomatch <= 1;
			end end
			// }}}
		2: begin // Match the second half of the source MAC address
			// {{{
			if (S_AXI_TDATA[31:16] != o_host_mac[15:0])
			begin
				tmp_mac[15:0] <= S_AXI_TDATA[31:16];
				nomatch <= 1;
			end end
			// }}}
		6: begin // Match source IP address
			// {{{
			if (S_AXI_TDATA != o_host_ip[31:0])
			begin
				tmp_ip <= S_AXI_TDATA;
				nomatch <= 1;
			end end
			// }}}
		8: begin // Match source UDP port
			// {{{
			if (S_AXI_TDATA[31:16] != o_host_udpport[15:0])
			begin
				tmp_sport <= S_AXI_TDATA[31:16];
				nomatch <= 1;
			end end
			// }}}
		10: begin // Sync on new frame
			// {{{
			if (S_AXI_TDATA[31:16] != 0 && nomatch)
				drop <= 1;
			else begin
				if (!i_handler_busy && !word_valid && !m_valid)
				begin
					o_host_mac <= tmp_mac;
					o_host_ip <= tmp_ip;
					o_host_udpport <= tmp_sport;
					o_host_frameid <= S_AXI_TDATA[31:16];
				end

				if (S_AXI_TDATA[31:16] == 0)
					drop <= 1;
				if (OPT_REPEAT_SUPPRESSION
					&& S_AXI_TDATA[31:16]== o_host_frameid
					&& o_host_frameid != 0)
				begin
					drop <= 1;
					o_repeat_stb <= 1'b1;
				end

				if (i_handler_busy || m_valid || word_valid || !r_syncd)
					{ drop, o_repeat_stb } <= 2'b10;

				o_gpio <= (o_gpio & ~(S_AXI_TDATA[15:8]
						| GPIO_AUTO_CLEAR))
					| (S_AXI_TDATA[15:8]& S_AXI_TDATA[7:0]);
			end end
			// }}}
		default: begin // Process (or skip) the payload data
			// {{{
			if (pktlen <= 4)
			begin
				nomatch <= 0;
				drop    <= 0;
			end end
			// }}}
		endcase
	end else begin
		o_repeat_stb <= 0;
	end

	initial	word_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		word_valid <= 0;
		word_last  <= 4'h0;
		word_data  <= 0;
		// }}}
	end else if (!word_valid || word_ready)
	begin
		word_valid <= 0;
		word_last  <= 4'h0;

		if (addr > 10 && !drop)
		begin
			word_valid <= S_AXI_TVALID && S_AXI_TREADY;
			word_data  <= S_AXI_TDATA;
			word_last[3] <= (pktlen == 1) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[2] <= (pktlen == 2) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[1] <= (pktlen == 3) && S_AXI_TVALID && S_AXI_TREADY;
			word_last[0] <= (pktlen == 4) && S_AXI_TVALID && S_AXI_TREADY;
		end
	end

	// On entrance, we know this packet is to us, its to our IP address,
	// its a UDP packet, and its to our UDP port.  Now we need to know
	// if it is a synch packet:
	// 1. It must have a frame ID of zero.
	initial	o_sync  = 1'b0;
	initial	r_syncd = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		o_sync <= 0;
		r_syncd <= 0;
	end else if (S_AXI_TVALID && S_AXI_TREADY && (addr == 10)
			&& (S_AXI_TDATA[31:16] == 0) && !i_handler_busy)
	begin
		o_sync <= 1'b1;
		r_syncd <= 1'b1;
	end else
		o_sync <= 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step #2: Break the incoming words into bytes for the payload handler
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	new_load = ~(word_last - 1);

	initial	m_valid = 0;
	initial	m_loaded = 0;
	initial m_last   = 0;
	initial	m_data   = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		m_valid  <= 0;
		m_loaded <= 0;
		m_last   <= 0;
		m_data   <= 0;
		// }}}
	end else if (!M_AXI_TVALID || M_AXI_TREADY)
	begin
		// {{{
		// Step everything forward by one byte by default
		m_loaded <= { m_loaded[1:0], 1'b0 };
		m_last   <= { m_last[2:0],   1'b0 };
		m_data   <= { m_data[23:0],  8'b0 };

		if (!m_loaded[2])
		begin
			m_valid <= word_valid;
			m_data <= word_data;
			if (word_last == 0)
				m_loaded  <= 3'h7;
			else
				m_loaded <= new_load[2:0];
			if (!word_valid)
				m_loaded <= 0;
			m_last <= word_last;
		end else
			m_valid <= m_loaded[2];
		// }}}
	end

	assign	M_AXI_TVALID = m_valid;
	assign	M_AXI_TDATA  = m_data[31:24];
	assign	M_AXI_TLAST  = m_last[3];
	// }}}

	assign	o_debug = {
			S_AXI_TVALID,
			M_AXI_TVALID, o_sync,
			nomatch, drop, i_handler_busy,

			S_AXI_TVALID, S_AXI_TREADY, m_loaded[2:0],
				addr[4:0], S_AXI_TDATA[15:0]
			};

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, new_load[3] };
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
`ifdef	FORMAL
`endif
endmodule
