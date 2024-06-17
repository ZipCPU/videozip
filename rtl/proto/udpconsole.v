////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/udpconsole.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	1) Assemble console packets into UDP packets, and 2) request
//		a console packet after sufficient data has arrived.
//
//	Console packets are requested if:
//	1. It's been a second (or longer) since the last one
//	2. There's been more than an 8th of a FIFO of data
//	3. Since the last data, there have been fewer than 7 packets, *AND*
//		at least an eigth of a second has passed.
//
//	The last criteria is to make sure we output console data at a rate of
//	(nearly) 8Hz as long as the console is active, but once the console
//	settles down, we'll go back down to a rate of 1Hz.
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
module udpconsole #(
		// {{{
		parameter	LGFIFO	= 10,
		parameter	MAXPKTLN = (1<<LGFIFO)-20-8-8,
		parameter [15:0]	CON_UDPPORT = 16'd8547,
		parameter [0:0]	OPT_SKIDBUFFER = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Host port info
		// {{{
		input	wire	[47:0]		i_host_mac,
		input	wire	[31:0]		i_my_ipaddr,
		input	wire	[31:0]		i_host_ip,
		// }}}
		// Console input
		// {{{
		input	wire			S_CON_VALID,
		output	wire			S_CON_READY,
		input	wire	[7:0]		S_CON_DATA,
		// }}}
		// Outgoing console packet data
		// {{{
		output	wire			M_CON_VALID,
		input	wire			M_CON_READY,
		output	wire	[31:0]		M_CON_DATA,
		output	wire			M_CON_LAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg				idle_timeout;
	reg	[26:0]			idle_time;
	reg	[$clog2(MAXPKTLN/8+1)-1:0]	char_count;
	reg					char_trigger;
	reg				minor_timeout;
	reg	[2:0]			minor_counter;
	wire			pkt_request, pkt_busy;
	wire	[LGFIFO-1:0]	pkt_reqlen;

	wire		con_valid, con_ready, con_last;
	wire	[7:0]	con_data;

	reg		wrd_valid, wrd_last;
	wire		wrd_ready;
	reg	[31:0]	wrd_data;
	reg	[1:0]	wrd_addr;

	wire		hdr_valid, hdr_ready, hdr_last;
	wire	[31:0]	hdr_data;

	wire	[31:0]	udp_debug;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet console (submodule)
	// {{{

	pktconsole #(
		.LGFIFO(LGFIFO),
		.MAXPKTLN(MAXPKTLN[LGFIFO-1:0]),
		.OPT_SKIDBUFFER(OPT_SKIDBUFFER),
		.OPT_LOWPOWER(OPT_LOWPOWER)
	) u_pktconsole (
		.i_clk(i_clk), .i_reset(i_reset),
		.S_CON_VALID(S_CON_VALID), .S_CON_READY(S_CON_READY),
			.S_CON_DATA(S_CON_DATA),
		.i_req(pkt_request), .o_busy(pkt_busy),
			.i_len(pkt_reqlen),
		.M_CON_VALID(con_valid), .M_CON_READY(con_ready),
			.M_CON_DATA(con_data), .M_CON_LAST(con_last)
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate packet requests
	// {{{

	assign		pkt_reqlen = MAXPKTLN[LGFIFO-1:0];

	always @(posedge i_clk)
	if (i_reset || con_valid)
		idle_time <= 0;
	else if (idle_time < 100_000_000)
		idle_time <= idle_time + 1;

	always @(posedge i_clk)
	if (i_reset || con_valid)
		idle_timeout <= 0;
	else
		idle_timeout <= (idle_time >= 100_000_000);

	always @(posedge i_clk)
	if (i_reset)
		minor_counter <= 0;
	else if (S_CON_VALID && S_CON_READY)
		minor_counter <= 7;
	else if (pkt_request && !pkt_busy && minor_counter > 0)
		minor_counter <= minor_counter - 1;

	always @(posedge i_clk)
	if (i_reset || con_valid)
		minor_timeout <= 0;
	else
		minor_timeout <= (minor_counter != 0)
					&& (idle_time >= 12_500_000);

	always @(posedge i_clk)
	if (i_reset || (pkt_request && !pkt_busy))
		char_count <= 0;
	else if (S_CON_VALID && S_CON_READY && !(&char_count))
		char_count <= char_count + 1;

	always @(posedge i_clk)
	if (i_reset || con_valid)
		char_trigger <= 0;
	else
		char_trigger <= (char_count > MAXPKTLN/8);

	assign	pkt_request = idle_timeout || char_trigger || minor_timeout;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Convert from a byte stream to a 32-bit stream
	// {{{

	always @(posedge i_clk)
	if (i_reset)
		wrd_addr <= 0;
	else if (con_valid && con_ready)
	begin
		wrd_addr <= wrd_addr + 1;
		if (con_last)
			wrd_addr <= 0;
	end

	always @(posedge i_clk)
	if (i_reset)
		wrd_valid <= 0;
	else if (!wrd_valid || wrd_ready)
		wrd_valid <= con_valid && (con_last || (wrd_addr == 2'b11));

	always @(posedge i_clk)
	if (i_reset)
		wrd_data <= 0;
	else if (!wrd_valid || wrd_ready)
	begin
		if (wrd_last)
			wrd_data <= 0;

		if (con_valid)
		case(wrd_addr[1:0])
		2'b00: wrd_data[31:24] <= con_data;
		2'b01: wrd_data[23:16] <= con_data;
		2'b10: wrd_data[15: 8] <= con_data;
		2'b11: wrd_data[ 7: 0] <= con_data;
		endcase
	end

	always @(posedge i_clk)
	if (i_reset)
		wrd_last <= 0;
	else if (!wrd_valid || wrd_ready)
		wrd_last <= con_valid && con_last;

	assign	con_ready = (!wrd_valid || wrd_ready);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate an IP header
	// {{{

	ipheader
	u_ipheader (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.i_enet_dest(i_host_mac), .i_ip_src(i_my_ipaddr),
				.i_ip_dest(i_host_ip),
		//
		.M_AXI_TVALID(hdr_valid), .M_AXI_TREADY(hdr_ready),
		.M_AXI_TDATA( hdr_data),  .M_AXI_TLAST( hdr_last)
		//
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Convert the console packet to UDP
	// {{{

	pkt2udp #(
		.LGMEM(LGFIFO)
	) u_pkt2udp (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(wrd_valid), .S_AXIN_READY(wrd_ready),
		.S_AXIN_DATA(wrd_data), .S_AXIN_LAST(wrd_last),
		.S_AXIN_ABORT(1'b0),
		//
		.S_HDR_VALID(hdr_valid), .S_HDR_READY(hdr_ready),
		.S_HDR_DATA(hdr_data), .S_HDR_LAST(hdr_last),
		//
		.i_udp_sport(CON_UDPPORT), .i_udp_dport(CON_UDPPORT),
		//
		.M_AXIS_VALID(M_CON_VALID), .M_AXIS_READY(M_CON_READY),
		.M_AXIS_DATA(M_CON_DATA), .M_AXIS_LAST(M_CON_LAST),
		//
		.o_debug(udp_debug)
		// }}}
	);

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, udp_debug };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
