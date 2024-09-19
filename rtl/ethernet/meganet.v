////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/meganet.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Tries to pull all the NET interfaces together into one
//		conglomerate that can handle multiple sources and sinks.
//
//
// Network interfaces include:
//		ARP, ICMP	- handled internally
//
//	DBG	-- UDP, to/from debugger
//	DATA	-- Data to the outside world, comes in UDP format.
//	CPU	-- Everything else gets handled by the CPU somehow (magically)
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
`timescale 1ns/1ps
// }}}
module	meganet #(
		// {{{
		// Select whether the outgoing debug wires are associated
		// with the receive or the transmit side of interface
		// localparam	[0:0]	RXSCOPE = 1'b0
		//
		// Just some random numbers drawn from thin air ...
		parameter [47:0]	DEF_HWMAC  = 48'h82_33_48_02,
		parameter [31:0]	DEF_IPADDR = 32'hc0_a8_07_89,
		parameter [15:0]	UDP_DBGPORT = 8545,
		// parameter [0:0]		OPT_NETTIME = 1'b0,
		parameter [0:0]		OPT_DEBUG = 1'b1	// 0 for RX,1TX
		// parameter [15:0]	UDP_DATAPORT = 8546
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire		S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		output	wire	[47:0]	o_hwmac,
		output	wire	[31:0]	o_ipaddr,
		//
		// The last IP address that ping'd us.  We'll use it to send
		// RX processing data to.
		output	wire	[47:0]	o_ping_hwmac,
		output	wire	[31:0]	o_ping_ipaddr,
		//
		// Wishbone: The network control interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[4:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	wire		o_wb_ack,
		output	wire	[31:0]	o_wb_data,
		// }}}
		// S_CPU_*: Incoming CPU AXIN interface @ 100MHz
		// {{{
		input	wire		S_CPU_VALID,
		output	wire		S_CPU_READY,
		input	wire	[31:0]	S_CPU_DATA,
		input	wire	[1:0]	S_CPU_BYTES,
		input	wire		S_CPU_LAST,
		input	wire		S_CPU_ABORT,	// == 0
		// }}}
		// S_DBG_*: Incoming debug packet interface @ 100MHz
		// {{{
		input	wire		S_DBG_VALID,
		output	wire		S_DBG_READY,
		input	wire	[31:0]	S_DBG_DATA,
		input	wire		S_DBG_LAST,
		// }}}
		// S_DATA_*: Incoming data interface @ 100MHz
		// {{{
		input	wire		S_DATA_VALID,
		output	wire		S_DATA_READY,
		input	wire	[31:0]	S_DATA_DATA,
		input	wire	[1:0]	S_DATA_BYTES,
		input	wire		S_DATA_LAST,
		// }}}
		// M_CPU_*: Outgoing CPU packet interface @ 100MHz
		// {{{
		output	wire		M_CPU_VALID,
		input	wire		M_CPU_READY,
		output	wire	[31:0]	M_CPU_DATA,
		output	wire	[1:0]	M_CPU_BYTES,
		output	wire		M_CPU_LAST,
		output	wire		M_CPU_ABORT,
		// }}}
		// M_DBG_*: Outgoing packet interface @ 100MHz
		// {{{
		output	wire		M_DBG_VALID,
		input	wire		M_DBG_READY,
		output	wire	[31:0]	M_DBG_DATA,
		output	wire	[1:0]	M_DBG_BYTES,
		output	wire		M_DBG_LAST,
		// output wire		M_DBG_ABORT,
		// }}}
		// PHY interface
		// {{{
		output	wire		o_net_reset_n,
		//
		input	wire		i_net_rx_clk, i_net_rx_dv, i_net_rx_err,
		input	wire	[7:0]	i_net_rxd,
		//
		input	wire		i_net_tx_clk,
		output	wire	[1:0]	o_net_tx_ck,
		output	wire		o_net_tx_ctl,
		output	wire	[7:0]	o_net_txd,
		// }}}
		//
		output	wire		o_debug_clk,
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	wire	i_clk = S_AXI_ACLK;
	wire	i_reset = !S_AXI_ARESETN;
	wire	rx_reset, tx_reset;

	wire		RX_VALID, RX_READY, RX_LAST, RX_ABORT;
	wire	[7:0]	RX_DATA;

	wire		TX_VALID, TX_READY;
	wire	[7:0]	TX_DATA;
	// Verilator lint_off UNUSED
	wire		TX_LAST, TX_ABORT;
	// Verilator lint_on  UNUSED

	wire	[31:0]	rx_arp_debug,  tx_arp_debug;
	wire	[31:0]	rx_icmp_debug, tx_icmp_debug;
	wire	[31:0]	data_debug;	// TX clock
	wire	[31:0]	rx_raw_debug,  tx_raw_debug;
	wire	[31:0]	dbgrx_debug;	// RX clock
	wire	[31:0]	dbgtx_debug;	// TX clock
	wire	[31:0]	rx_split_debug, tx_merge_debug;	// TX clock
	wire	[31:0]	core_debug;	// core_debug_clk
	wire		core_debug_clk;

	wire	[31:0]	rx_my_ipaddr;

	wire		net_stb, net_ack, net_stall;
	wire	[31:0]	net_data;

	wire	[2:0]	w_debugsel;

	reg	[31:0]	rx_debug, tx_debug;
	wire	[2:0]	n_rx_debugsel, n_tx_debugsel;
	wire		ign_tfrrxdbg_valid, ign_tfrrxdbg_ready;
	wire		ign_tfrtxdbg_valid, ign_tfrtxdbg_ready;
	wire	[3:0]	arp_low_debug;
	reg		merge_trigger, merge_last;
	reg		last_tx_active;
	wire		high_speed_net;

	////////////////////////////////////////
	//
	// ARP declarations
	// {{{
	wire		ARPRX_VALID, ARPRX_READY, ARPRX_LAST, ARPRX_ABORT;
	wire	[7:0]	ARPRX_DATA;
	wire		ARPTX_VALID, ARPTX_READY, ARPTX_LAST, ARPTX_ABORT;
	wire	[7:0]	ARPTX_DATA;
	wire	[0:0]	ARPTX_BYTES;
	wire		ARP_VALID, ARP_READY, ARP_LAST, ARP_ABORT;
	wire	[7:0]	ARP_DATA;
	wire		ARPS_VALID, ARPS_READY, ARPS_LAST, ARPS_ABORT,
			ARPS_BYTES;
	wire	[7:0]	ARPS_DATA;
	wire		arp_no_match, arp_match;
	// }}}
	////////////////////////////////////////
	//
	// ICMP declarations
	// {{{
	wire		ICMPRX_VALID, ICMPRX_READY, ICMPRX_LAST, ICMPRX_ABORT;
	wire	[7:0]	ICMPRX_DATA;
	wire		ICMPTX_VALID, ICMPTX_READY, ICMPTX_LAST, ICMPTX_ABORT;
	wire	[7:0]	ICMPTX_DATA;
	wire		ICMPTX_BYTES;
	wire		ICMP_VALID, ICMP_READY, ICMP_LAST, ICMP_ABORT;
	wire	[7:0]	ICMP_DATA;
	wire		ICMPS_VALID, ICMPS_READY, ICMPS_LAST, ICMPS_ABORT,
			ICMPS_BYTES;
	wire	[7:0]	ICMPS_DATA;
	wire		icmp_no_match, icmp_match;
	// }}}
	////////////////////////////////////////
	//
	// NTP declarations
	// {{{
	// }}}
	////////////////////////////////////////
	//
	// CPU channel declarations
	// {{{
	wire		CPUCK_VALID, CPUCK_READY, CPUCK_LAST, CPUCK_ABORT;
	wire	[31:0]	CPUCK_DATA;
	wire	[1:0]	CPUCK_BYTES;

	// Verilator lint_off UNUSED
	wire		CPURX_VALID, CPURX_READY, CPURX_LAST, CPURX_ABORT;
	wire	[7:0]	CPURX_DATA;
	// Verilator lint_on  UNUSED
	wire		cpu_no_match, cpu_match, ip_no_match;

	wire		CPUBUS_VALID, CPUBUS_READY, CPUBUS_LAST, CPUBUS_ABORT;
	wire	[31:0]	CPUBUS_DATA;
	wire	[2:0]	CPUBUS_BYTES;


	wire		CPUS_VALID, CPUS_READY, CPUS_LAST, CPUS_ABORT;
	wire	[7:0]	CPUS_DATA;
	wire	[0:0]	CPUS_BYTES;
	// }}}
	////////////////////////////////////////
	//
	// Debug channel declarations
	// {{{
	wire		DBGRX_VALID, DBGRX_READY, DBGRX_LAST, DBGRX_ABORT;
	wire	[7:0]	DBGRX_DATA;
	wire		DBG_VALID, DBG_READY, DBG_LAST, DBG_ABORT;
	wire	[7:0]	DBG_DATA;
	wire		DBGW_VALID, DBGW_READY, DBGW_LAST, DBGW_ABORT;
	wire	[31:0]	DBGW_DATA;
	wire	[2:0]	DBGW_BYTES;
	wire		DBGN_VALID, DBGN_READY, DBGN_LAST, DBGN_ABORT;
	wire	[31:0]	DBGN_DATA;
	wire	[1:0]	DBGN_BYTES;
	//
	wire		DBGS_VALID, DBGS_READY, DBGS_LAST, DBGS_ABORT;
	wire	[7:0]	DBGS_DATA;
	wire	[0:0]	DBGS_BYTES;
	//
	wire		DBGCK_VALID, DBGCK_READY, DBGCK_LAST, DBGCK_ABORT;
	wire	[31:0]	DBGCK_DATA;
	wire	[1:0]	DBGCK_BYTES;
	//
	wire		dbg_no_match, dbg_match;
	wire		M_DBG_ABORT;

	// }}}
	////////////////////////////////////////
	//
	// Data channel declarations
	// {{{
	wire		DATACK_VALID, DATACK_READY, DATACK_ABORT, DATACK_LAST;
	wire	[31:0]	DATACK_DATA;
	wire	[1:0]	DATACK_BYTES;
	wire		DATAS_VALID, DATAS_READY, DATAS_LAST, DATAS_ABORT;
	wire	[7:0]	DATAS_DATA;
	wire	[0:0]	DATAS_BYTES;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Merge transmit packet sources into a single stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	pktmerge #(
		.NS(5), .DW(8)
	) u_pktmerge (
		// {{{
		.i_clk(i_net_tx_clk), .i_reset(tx_reset),
		.S_AXIN_VALID({ ARPS_VALID, ICMPS_VALID, CPUS_VALID, DBGS_VALID, DATAS_VALID }),
		.S_AXIN_READY({ ARPS_READY, ICMPS_READY, CPUS_READY, DBGS_READY, DATAS_READY }),
		.S_AXIN_DATA({  ARPS_DATA,  ICMPS_DATA,   CPUS_DATA,  DBGS_DATA,  DATAS_DATA }),
		.S_AXIN_LAST({  ARPS_LAST,  ICMPS_LAST,   CPUS_LAST,  DBGS_LAST,  DATAS_LAST }),
		.S_AXIN_ABORT({ ARPS_ABORT, ICMPS_ABORT, CPUS_ABORT, DBGS_ABORT, DATAS_ABORT }),

		.M_AXIN_VALID(TX_VALID),
		.M_AXIN_READY(TX_READY),
		.M_AXIN_DATA( TX_DATA),
		.M_AXIN_LAST( TX_LAST),
		.M_AXIN_ABORT(TX_ABORT)
		// }}}
	);

	always @(posedge i_net_tx_clk)
		merge_last <= |{ ARPS_VALID, ICMPS_VALID, CPUS_VALID, DBGS_VALID, DATAS_VALID };

	always @(posedge i_net_tx_clk)
		merge_trigger <= !merge_last && |{ ARPS_VALID, ICMPS_VALID, CPUS_VALID, DBGS_VALID, DATAS_VALID };

	assign	tx_merge_debug = {
		merge_trigger, merge_trigger, 1'b0, merge_last,
		ARPS_VALID,  ARPS_READY,  ARPS_LAST,  ARPS_ABORT,
		ICMPS_VALID, ICMPS_READY, ICMPS_LAST, ICMPS_ABORT,
		4'h0, // NTPTX_VALID, NTPTX_READY, NTPTX_LAST, NTPTX_ABORT,
		CPUS_VALID,  CPUS_READY,  CPUS_LAST,  CPUS_ABORT,
		DBGS_VALID,  DBGS_READY,  DBGS_LAST,  DBGS_ABORT,
		DATAS_VALID, DATAS_READY, DATAS_LAST, DATAS_ABORT,
		TX_VALID,    TX_READY,    TX_LAST, 1'b0
		};

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Split receive packet sources into multiple outgoing packet streams
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Internal -> pktsplitter ->
	//	arp.v -> ARP_*
	//	icmpecho.v -> ICMP_*
	//	NTP?
	//	CPU?
	//	DBG?
	//	(No data in pktsplitter)
	//

	pktsplitter #(
		.NUM_SINKS(4)
	) rxsplitter (
		// {{{
		.S_AXI_ACLK(i_net_rx_clk), .S_AXI_ARESETN(!rx_reset),
		//
		.S_AXIN_VALID(RX_VALID), .S_AXIN_READY(RX_READY),
			.S_AXIN_DATA(RX_DATA), .S_AXIN_LAST(RX_LAST),
			.S_AXIN_ABORT(RX_ABORT),
		//
		.M_AXIN_VALID({ ARPRX_VALID, ICMPRX_VALID,
				CPURX_VALID, DBGRX_VALID }),
		.M_AXIN_READY({ ARPRX_READY, ICMPRX_READY,
				CPURX_READY, DBGRX_READY }),
		.M_AXIN_DATA({ ARPRX_DATA, ICMPRX_DATA,
				CPURX_DATA, DBGRX_DATA }),
		.M_AXIN_LAST({ ARPRX_LAST, ICMPRX_LAST,
				CPURX_LAST, DBGRX_LAST }),
		.M_AXIN_ABORT({ ARPRX_ABORT, ICMPRX_ABORT,
				CPURX_ABORT, DBGRX_ABORT }),
		.i_match({ arp_match,
				(icmp_match && !ip_no_match),
				(cpu_match  && !ip_no_match),
				(dbg_match  && !ip_no_match) }),
		.i_no_match({ arp_no_match,
				(icmp_no_match || ip_no_match),
				(cpu_no_match  || ip_no_match),
				(dbg_no_match  || ip_no_match) })
		// }}}
	);

	assign	rx_split_debug = {
		RX_VALID, 3'h0,
		ARPRX_VALID,  ARPRX_READY,  ARPRX_LAST,  ARPRX_ABORT,
		ICMPRX_VALID, ICMPRX_READY, ICMPRX_LAST, ICMPRX_ABORT,
		4'h0, // NTPRX_VALID,  NTPRX_READY,  NTPRX_LAST,  NTPRX_ABORT,
		CPURX_VALID,  CPURX_READY,  CPURX_LAST,  CPURX_ABORT,
		DBGRX_VALID,  DBGRX_READY,  DBGRX_LAST,  DBGRX_ABORT,
		4'h0,
		RX_VALID,    RX_READY,    RX_LAST, RX_ABORT
		};


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ARP handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Recognize and generate an ARP response

	arp
	u_arp (
		// {{{
		.S_AXI_ACLK(i_net_rx_clk), .S_AXI_ARESETN(!rx_reset),
		//
		.S_AXIN_VALID( ARPRX_VALID ),
		.S_AXIN_READY( ARPRX_READY ),
		.S_AXIN_DATA(  ARPRX_DATA ),
		.S_AXIN_LAST(  ARPRX_LAST ),
		.S_AXIN_ABORT( ARPRX_ABORT ),
		//
		.M_AXIN_VALID( ARP_VALID ),
		.M_AXIN_READY( ARP_READY ),
		.M_AXIN_DATA(  ARP_DATA  ),
		.M_AXIN_LAST(  ARP_LAST  ),
		.M_AXIN_ABORT( ARP_ABORT ),
		//
		.i_hwmac(o_hwmac),
		.i_ipaddr(o_ipaddr),
		.o_match(arp_match),
		.o_no_match(arp_no_match),
		.o_debug(arp_low_debug)
		// }}}
	);

	assign	rx_arp_debug = {
			(arp_match || arp_no_match), TX_VALID,
			arp_match, arp_no_match,
			arp_low_debug, // 4'h0,
		ARPRX_VALID, ARPRX_READY, ARPRX_LAST, ARPRX_ABORT, ARPRX_DATA,
		ARP_VALID, ARP_READY, ARP_LAST, ARP_ABORT, ARP_DATA
			};

	// Move the ARP response packet from the RX to the TX clock domain
	axincdc #(
		.LGFIFO(3), .DW(8)
	) arp_cdc (
		// {{{
		.S_CLK(i_net_rx_clk), .S_ARESETN(!rx_reset),
		.S_VALID(ARP_VALID), .S_READY(ARP_READY),
			.S_DATA(ARP_DATA), .S_BYTES(1'b1),
			.S_ABORT(ARP_ABORT), .S_LAST(ARP_LAST),
		//
		.M_CLK(i_net_tx_clk), .M_ARESETN(!tx_reset),
		.M_VALID(ARPTX_VALID), .M_READY(ARPTX_READY),
			.M_DATA(ARPTX_DATA), .M_BYTES(ARPTX_BYTES),
			.M_ABORT(ARPTX_ABORT), .M_LAST(ARPTX_LAST)
		//
		// }}}
	);

	// Unwrap the packet in the TX domain for transmission
	pktgate #(
		.DW(8), .LGFLEN(8), .OPT_DROP_ON_OVERFLOW(1'b1)
	) u_arpgate (
		// {{{
		.S_AXI_ACLK(i_net_tx_clk), .S_AXI_ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(ARPTX_VALID),
		.S_AXIN_READY(ARPTX_READY),
		.S_AXIN_DATA( ARPTX_DATA),
		.S_AXIN_BYTES(ARPTX_BYTES),
		.S_AXIN_LAST( ARPTX_LAST),
		.S_AXIN_ABORT(ARPTX_ABORT),
		//
		.M_AXIN_VALID(ARPS_VALID),
		.M_AXIN_READY(ARPS_READY),
		.M_AXIN_DATA( ARPS_DATA),
		.M_AXIN_BYTES(ARPS_BYTES),
		.M_AXIN_LAST( ARPS_LAST),
		.M_AXIN_ABORT(ARPS_ABORT)
		// }}}
	);

	assign	tx_arp_debug = {
		arp_match, TX_VALID,
		ARPTX_VALID, ARPTX_READY, 8'h0, ARPTX_DATA,
		ARPS_VALID, ARPS_READY, ARPS_LAST, ARPS_ABORT, ARPS_DATA
		};

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ICMP handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Recognize an ICMP request and generate an ICMP response
	icmpecho
	u_icmp (
		// {{{
		.S_AXI_ACLK(i_net_rx_clk), .S_AXI_ARESETN(!rx_reset),
		//
		.S_AXIN_VALID( ICMPRX_VALID ),
		.S_AXIN_READY( ICMPRX_READY ),
		.S_AXIN_DATA(  ICMPRX_DATA ),
		.S_AXIN_LAST(  ICMPRX_LAST ),
		.S_AXIN_ABORT( ICMPRX_ABORT ),
		//
		.M_AXIN_VALID( ICMP_VALID ),
		.M_AXIN_READY( ICMP_READY ),
		.M_AXIN_DATA(  ICMP_DATA  ),
		.M_AXIN_LAST(  ICMP_LAST  ),
		.M_AXIN_ABORT( ICMP_ABORT ),
		//
		// .i_hwmac(o_hwmac),
		.i_ipaddr(rx_my_ipaddr),
		.o_match(icmp_match),
		.o_no_match(icmp_no_match),
		//
		.o_ping_mac(o_ping_hwmac),
		.o_ping_ipaddr(o_ping_ipaddr),
		.o_debug(rx_icmp_debug)
		// }}}
	);

	/*
	assign	rx_icmp_debug = {
			(icmp_match || icmp_no_match), 1'b0,
			icmp_match, icmp_no_match,
			4'h0,
		ICMPRX_VALID, ICMPRX_READY, ICMPRX_LAST, ICMPRX_ABORT, ICMPRX_DATA,
		ICMP_VALID, ICMP_READY, ICMP_LAST, ICMP_ABORT, ICMP_DATA
			};
	*/

	// Move the ICMP response packet from the RX to the TX clock domain
	axincdc #(
		.LGFIFO(3), .DW(8)
	) icmp_cdc (
		// {{{
		.S_CLK(i_net_rx_clk), .S_ARESETN(!rx_reset),
		.S_VALID(ICMP_VALID), .S_READY(ICMP_READY),
			.S_DATA(ICMP_DATA), .S_BYTES(1'b1),
			.S_ABORT(ICMP_ABORT), .S_LAST(ICMP_LAST),
		//
		.M_CLK(i_net_tx_clk), .M_ARESETN(!tx_reset),
		.M_VALID(ICMPTX_VALID), .M_READY(ICMPTX_READY),
			.M_DATA(ICMPTX_DATA), .M_BYTES(ICMPTX_BYTES),
			.M_ABORT(ICMPTX_ABORT), .M_LAST(ICMPTX_LAST)
		// }}}
	);

	// Buffer the packet in the TX domain for transmission
	//  .. Wait for the whole packet before transmitting
	pktgate #(
		.DW(8), .LGFLEN(8), .OPT_DROP_ON_OVERFLOW(1'b1)
	) u_icmpgate (
		// {{{
		.S_AXI_ACLK(i_net_tx_clk), .S_AXI_ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(ICMPTX_VALID),
		.S_AXIN_READY(ICMPTX_READY),
		.S_AXIN_DATA( ICMPTX_DATA),
		.S_AXIN_BYTES(ICMPTX_BYTES),
		.S_AXIN_LAST( ICMPTX_LAST),
		.S_AXIN_ABORT(ICMPTX_ABORT),
		//
		.M_AXIN_VALID(ICMPS_VALID),
		.M_AXIN_READY(ICMPS_READY),
		.M_AXIN_DATA( ICMPS_DATA),
		.M_AXIN_BYTES(ICMPS_BYTES),
		.M_AXIN_LAST( ICMPS_LAST),
		.M_AXIN_ABORT(ICMPS_ABORT)
		// }}}
	);

	assign	tx_icmp_debug = {
		ICMPTX_VALID && ICMPTX_READY,
		ICMPTX_VALID, ICMPTX_READY, 10'h0, ICMPTX_DATA,
		ICMPS_VALID, ICMPS_READY, ICMPS_LAST, ICMPS_DATA
		};

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// DBG handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	////
	//// RX (incoming request) Handling
	////
	//// {{{

	// Look for UDP packets sent to UDP_DBGPORT
	udpmatch
	u_dbg_match (
		// {{{
		.S_AXI_ACLK(i_net_rx_clk), .S_AXI_ARESETN(!rx_reset),
		//
		.S_AXIN_VALID( DBGRX_VALID ),
		.S_AXIN_READY( DBGRX_READY ),
		.S_AXIN_DATA(  DBGRX_DATA ),
		.S_AXIN_LAST(  DBGRX_LAST ),
		.S_AXIN_ABORT( DBGRX_ABORT ),
		//
		.M_AXIN_VALID( DBG_VALID ),
		.M_AXIN_READY( DBG_READY ),
		.M_AXIN_DATA(  DBG_DATA  ),
		.M_AXIN_LAST(  DBG_LAST  ),
		.M_AXIN_ABORT( DBG_ABORT ),
		//
		.i_udpport(UDP_DBGPORT),
		.o_match(dbg_match),
		.o_no_match(dbg_no_match)
		// }}}
	);

	assign	dbgrx_debug = {
		DBGRX_VALID && DBGRX_READY, dbg_match, dbg_no_match, 1'b0,
		RX_VALID, RX_READY, RX_LAST, RX_ABORT,
		DBGRX_VALID, DBGRX_READY, DBGRX_LAST, DBGRX_ABORT, DBGRX_DATA,
		DBG_VALID, DBG_READY, DBG_LAST, DBG_ABORT, DBG_DATA
		};

	// Adjust the width to 32b words--necessary to cross clock domains
	axinwidth #(
		.IW(8), .OW(32), .OPT_LITTLE_ENDIAN(1'b0)
	) u_dbgrx_width (
		// {{{
		.ACLK(i_net_rx_clk), .ARESETN(!rx_reset),
		//
		.S_AXIN_VALID( DBG_VALID ), .S_AXIN_READY( DBG_READY ),
		.S_AXIN_DATA(  DBG_DATA  ), .S_AXIN_BYTES( 1'b1  ),
		.S_AXIN_LAST(  DBG_LAST  ), .S_AXIN_ABORT( DBG_ABORT ),
		//
		.M_AXIN_VALID(DBGW_VALID), .M_AXIN_READY(DBGW_READY),
			.M_AXIN_DATA(DBGW_DATA), .M_AXIN_BYTES(DBGW_BYTES),
			.M_AXIN_LAST(DBGW_LAST), .M_AXIN_ABORT(DBGW_ABORT)
		// }}}
	);

	// Discard anything but whole packets
	pktgate #(
		.DW(32), .LGFLEN(9), .OPT_DROP_ON_OVERFLOW(1'b1)
	) u_dbggate (
		// {{{
		.S_AXI_ACLK(i_net_tx_clk), .S_AXI_ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(DBGW_VALID), .S_AXIN_READY(DBGW_READY),
		.S_AXIN_DATA( DBGW_DATA), .S_AXIN_BYTES(DBGW_BYTES[1:0]),
		.S_AXIN_LAST( DBGW_LAST), .S_AXIN_ABORT(DBGW_ABORT),
		//
		.M_AXIN_VALID(DBGN_VALID), .M_AXIN_READY(DBGN_READY),
		.M_AXIN_DATA( DBGN_DATA),  .M_AXIN_BYTES(DBGN_BYTES),
		.M_AXIN_LAST( DBGN_LAST),  .M_AXIN_ABORT(DBGN_ABORT)
		// }}}
	);

	// Move to the system/bus clock domain
	axincdc #(
		.LGFIFO(3), .DW(32)
	) u_dbg_cdc2bus (
		// {{{
		.S_CLK(i_net_rx_clk), .S_ARESETN(!rx_reset),
		.S_VALID(DBGN_VALID), .S_READY(DBGN_READY),
			.S_DATA(DBGN_DATA), .S_BYTES(DBGN_BYTES),
			.S_ABORT(DBGN_ABORT), .S_LAST(DBGN_LAST),
		//
		.M_CLK(S_AXI_ACLK), .M_ARESETN(S_AXI_ARESETN),
		.M_VALID(M_DBG_VALID), .M_READY(M_DBG_READY),
			.M_DATA(M_DBG_DATA), .M_BYTES(M_DBG_BYTES),
			.M_ABORT(M_DBG_ABORT), .M_LAST(M_DBG_LAST)
		// }}}
	);

	//// }}}
	////
	//// TX (return) handling
	////
	//// {{{

	// Packet comes in as AXI stream from off module.

	// Convert the incoming DBG packet from the system to the transmit clock
	axincdc #(
		.LGFIFO(3), .DW(32)
	) u_dbgtx_cdc (
		// {{{
		.S_CLK(i_clk), .S_ARESETN(!i_reset),
		.S_VALID(S_DBG_VALID), .S_READY(S_DBG_READY),
			.S_DATA(S_DBG_DATA), .S_BYTES(2'b00),
			.S_ABORT(1'b0), .S_LAST(S_DBG_LAST),
		//
		.M_CLK(i_net_tx_clk), .M_ARESETN(!tx_reset),
		.M_VALID(DBGCK_VALID), .M_READY(DBGCK_READY),
			.M_DATA(DBGCK_DATA), .M_BYTES(DBGCK_BYTES),
			.M_ABORT(DBGCK_ABORT), .M_LAST(DBGCK_LAST)
		// }}}
	);

	// Now convert the packet from 32b to 8b for transmission
	axinwidth #(
		.IW(32), .OW(8), .OPT_LITTLE_ENDIAN(1'b0)
	) u_dbgtx_width (
		// {{{
		.ACLK(i_net_tx_clk), .ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(DBGCK_VALID), .S_AXIN_READY(DBGCK_READY),
		.S_AXIN_DATA( DBGCK_DATA), .S_AXIN_BYTES({
			((DBGCK_BYTES == 0) ? 1'b1:1'b0), DBGCK_BYTES }),
		.S_AXIN_LAST( DBGCK_LAST),  .S_AXIN_ABORT(DBGCK_ABORT),
		//
		.M_AXIN_VALID(DBGS_VALID), .M_AXIN_READY(DBGS_READY),
		.M_AXIN_DATA( DBGS_DATA),  .M_AXIN_BYTES(DBGS_BYTES),
		.M_AXIN_LAST( DBGS_LAST),  .M_AXIN_ABORT(DBGS_ABORT)
		// }}}
	);

	assign	dbgtx_debug = {
		DBGS_VALID && DBGS_READY, DBGCK_VALID, DBGCK_READY,
			DBGCK_DATA[4:0],
		DBGS_VALID, DBGS_READY, DBGS_LAST, DBGS_ABORT, DBGS_DATA,
		TX_VALID, TX_READY, TX_LAST, TX_ABORT, TX_DATA
		};


	///// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CPU handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	////
	//// Receive (incoming) handling
	////
	//// {{{

	// First, match: is this our packet?
	// {{{
	ipmatch
	u_ip_addr_check (
		.i_clk(i_net_rx_clk), .i_reset(rx_reset),
		//
		.i_ipaddr(rx_my_ipaddr),
		//
		.S_AXIN_VALID(RX_VALID && RX_READY),
		.S_AXIN_DATA(RX_DATA),
		.S_AXIN_LAST(RX_LAST),
		.S_AXIN_ABORT(RX_ABORT),
		.o_no_match(ip_no_match)
	);

	assign	cpu_no_match = ip_no_match;

	assign	cpu_match=({ arp_match, icmp_match, dbg_match } == 0)
				&& RX_LAST;

	// If something else has matched, we'll get an abort signal, and thus
	// never finish generating an AXI stream packet
	// }}}

	// Widen from 8b to 32b, so we can switch clock domains
	axinwidth #(
		.IW(8), .OW(32), .OPT_LITTLE_ENDIAN(1'b0)
	) u_cpurx_width (
		// {{{
		.ACLK(i_net_rx_clk), .ARESETN(!rx_reset),
		//
		.S_AXIN_VALID( CPURX_VALID ),
		.S_AXIN_READY( CPURX_READY ),
		.S_AXIN_DATA(  CPURX_DATA  ),
		.S_AXIN_BYTES( 1'b1  ),
		.S_AXIN_LAST(  CPURX_LAST  ),
		.S_AXIN_ABORT( CPURX_ABORT ),
		//
		.M_AXIN_VALID(CPUBUS_VALID), .M_AXIN_READY(CPUBUS_READY),
			.M_AXIN_DATA(CPUBUS_DATA), .M_AXIN_BYTES(CPUBUS_BYTES),
			.M_AXIN_LAST(CPUBUS_LAST), .M_AXIN_ABORT(CPUBUS_ABORT)
		// }}}
	);

	// Cross to the bus clock domain
	axincdc #(
		.LGFIFO(3), .DW(32)
	) u_cpu_cdc2bus (
		// {{{
		.S_CLK(i_net_rx_clk), .S_ARESETN(!rx_reset),
		.S_VALID(CPUBUS_VALID), .S_READY(CPUBUS_READY),
			.S_DATA(CPUBUS_DATA), .S_BYTES(CPUBUS_BYTES[1:0]),
			.S_ABORT(CPUBUS_ABORT), .S_LAST(CPUBUS_LAST),
		//
		.M_CLK(S_AXI_ACLK), .M_ARESETN(S_AXI_ARESETN),
		.M_VALID(M_CPU_VALID), .M_READY(M_CPU_READY),
			.M_DATA(M_CPU_DATA), .M_BYTES(M_CPU_BYTES),
			.M_ABORT(M_CPU_ABORT), .M_LAST(M_CPU_LAST)
		// }}}
	);

	//// }}}
	////
	//// Transmit (outgoing) packets from the CPU
	////
	//// {{{

	// Convert the incoming CPU packet to the transmit clock
	axincdc #(
		.LGFIFO(3), .DW(32)
	) cputx_afifo (
		// {{{
		.S_CLK(i_clk), .S_ARESETN(!i_reset),
		.S_VALID(S_CPU_VALID), .S_READY(S_CPU_READY),
			.S_DATA(S_CPU_DATA), .S_BYTES(S_CPU_BYTES),
			.S_LAST(S_CPU_LAST), .S_ABORT(S_CPU_ABORT),
		//
		.M_CLK(i_net_tx_clk), .M_ARESETN(!tx_reset),
		.M_VALID(CPUCK_VALID), .M_READY(CPUCK_READY),
			.M_DATA(CPUCK_DATA), .M_BYTES(CPUCK_BYTES),
			.M_LAST(CPUCK_LAST), .M_ABORT(CPUCK_ABORT)
		// }}}
	);

	// Convert from 32b to 8b
	axinwidth #(
		.IW(32), .OW(8), .OPT_LITTLE_ENDIAN(1'b0)
	) u_cputx_width (
		// {{{
		.ACLK(i_net_tx_clk), .ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(CPUCK_VALID), .S_AXIN_READY(CPUCK_READY),
		.S_AXIN_DATA( CPUCK_DATA), .S_AXIN_BYTES({
			((CPUCK_BYTES == 0) ? 1'b1:1'b0), CPUCK_BYTES }),
		.S_AXIN_LAST( CPUCK_LAST),  .S_AXIN_ABORT(CPUCK_ABORT),
		//
		.M_AXIN_VALID(CPUS_VALID), .M_AXIN_READY(CPUS_READY),
		.M_AXIN_DATA( CPUS_DATA),  .M_AXIN_BYTES(CPUS_BYTES),
		.M_AXIN_LAST( CPUS_LAST),  .M_AXIN_ABORT(CPUS_ABORT)
		// }}}
	);

	//// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outging DATA channel handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Cross to the TX clock domain
	axincdc #(
		.LGFIFO(3), .DW(32)
	) data_cdc (
		// {{{
		.S_CLK(i_clk), .S_ARESETN(!i_reset),
		.S_VALID(S_DATA_VALID), .S_READY(S_DATA_READY),
			.S_DATA(S_DATA_DATA), .S_BYTES(S_DATA_BYTES),
			.S_ABORT(1'b0), .S_LAST(S_DATA_LAST),
		//
		.M_CLK(i_net_tx_clk), .M_ARESETN(!tx_reset),
		.M_VALID(DATACK_VALID), .M_READY(DATACK_READY),
			.M_DATA(DATACK_DATA), .M_BYTES(DATACK_BYTES),
			.M_ABORT(DATACK_ABORT), .M_LAST(DATACK_LAST)
		// }}}
	);

	// Resize us down to 8b.  This should also provide sufficient
	// backpressure that we (shouldn't) need a gate
	axinwidth #(
		.IW(32), .OW(8)
	) u_datatx_width (
		// {{{
		.ACLK(i_net_tx_clk), .ARESETN(!tx_reset),
		//
		.S_AXIN_VALID(DATACK_VALID), .S_AXIN_READY(DATACK_READY),
		.S_AXIN_DATA( DATACK_DATA), .S_AXIN_BYTES({ (DATACK_BYTES==0),
				DATACK_BYTES }),
		.S_AXIN_LAST( DATACK_LAST), .S_AXIN_ABORT(DATACK_ABORT),
		//
		.M_AXIN_VALID(DATAS_VALID), .M_AXIN_READY(DATAS_READY),
		.M_AXIN_DATA( DATAS_DATA), .M_AXIN_BYTES(DATAS_BYTES),
		.M_AXIN_LAST( DATAS_LAST), .M_AXIN_ABORT(DATAS_ABORT)
		// }}}
	);

	assign	data_debug = {
		DATAS_VALID && DATAS_READY, // 3'b0, 4'h0,
		DATACK_VALID, DATACK_READY, DATACK_DATA[6:2],
		DATAS_VALID, DATAS_READY, DATAS_LAST, DATAS_ABORT, DATAS_DATA,
		TX_VALID,    TX_READY,    TX_LAST,    TX_ABORT,    TX_DATA
		};

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// NTP handling (none for now)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Network Core raw/bare packet handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	enetstream #(
		// {{{
		.RXSCOPE(!OPT_DEBUG),
		.DEF_HWMAC(DEF_HWMAC),
		.DEF_IPADDR(DEF_IPADDR)
		// }}}
	) net_core (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(!i_reset),
		//
		.o_tx_reset(tx_reset), .o_rx_reset(rx_reset),
		.o_rx_my_ipaddr(rx_my_ipaddr),
		.o_high_speed(high_speed_net),
		//
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(net_stb), .i_wb_we(i_wb_we),
			.i_wb_addr(i_wb_addr[2:0]),
				.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
			.o_wb_stall(net_stall),
				.o_wb_ack(net_ack), .o_wb_data(net_data),
		//
		// CLOCK: i_net_tx_clk
		.S_AXI_TVALID(TX_VALID), .S_AXI_TREADY(TX_READY),
			.S_AXI_TDATA(TX_DATA),
		//
		// CLOCK: i_net_rx_clk
		.M_AXIN_VALID(RX_VALID), .M_AXIN_READY(RX_READY),
			.M_AXIN_DATA(RX_DATA),
			.M_AXIN_LAST(RX_LAST), .M_AXIN_ABORT(RX_ABORT),
		//
		.o_net_reset_n(o_net_reset_n),
		.i_net_rx_clk(i_net_rx_clk), .i_net_rx_dv(i_net_rx_dv),
			.i_net_rx_err(i_net_rx_err), .i_net_rxd(i_net_rxd),
		.i_net_tx_clk(i_net_tx_clk), .o_net_tx_ck(o_net_tx_ck),
			.o_net_tx_ctl(o_net_tx_ctl), .o_net_txd(o_net_txd),
		//
		.o_hw_mac(o_hwmac),
		.o_ipaddr(o_ipaddr),
		//
		.o_debug_clk(core_debug_clk), .o_debug(core_debug)
		// }}}
	);

	always @(posedge i_net_tx_clk)
	if (tx_reset)
		last_tx_active <= 0;
	else
		last_tx_active <= TX_VALID && TX_READY;

	assign	rx_raw_debug = {
		(TX_VALID && !last_tx_active), 10'h0,
		TX_VALID, TX_READY, TX_LAST, TX_ABORT, TX_DATA,
			o_net_tx_ctl, o_net_txd
		};

	assign	tx_raw_debug = {
		(TX_VALID && !last_tx_active), 10'h0,
		TX_VALID, TX_READY, TX_LAST, TX_ABORT, TX_DATA,
			o_net_tx_ctl, o_net_txd
		};
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Performance counters
	// {{{
`define	PERF_COUNTER
`ifdef	PERF_COUNTER
	// {{{
	// Local declarations
	// {{{
	reg	[31:0]	pkts_rcvd, arp_packets_rcvd, icmp_packets_rcvd,
			dbg_packets_rcvd;
	reg	[31:0]	pkts_tx, arp_packets_tx, icmp_packets_tx,
			data_packets_tx, tx_aborts, dbg_packets_tx;
	reg		icmp_active, arp_active, dbg_active;
	reg	[2:0]	r_debugsel;

	wire	[31:0]	wb_pkts_rcvd, wb_arp_packets_rcvd, wb_icmp_packets_rcvd,
			wb_dbg_packets_rcvd;

	wire	[31:0]	wb_pkts_tx, wb_arp_packets_tx, wb_icmp_packets_tx,
				wb_data_packets_tx, wb_tx_aborts,
				wb_dbg_packets_tx;

	wire	ign_tfrrx_ready, ign_tfrrx_valid;
	wire	ign_tfrtx_ready, ign_tfrtx_valid;

	reg		ack_pipe, wb_ack;
	reg		pipe_src;
	reg	[31:0]	pipe_data, wb_data;
	reg	[5:0]	tx_in_progress;
	// }}}

	////
	//// Receive (incoming) handling
	////
	// {{{
	always @(posedge i_net_rx_clk)
	if (rx_reset)
		pkts_rcvd <= 0;
	else if (RX_VALID && RX_READY && RX_LAST && !RX_ABORT)
		pkts_rcvd <= pkts_rcvd + 1;

	always @(posedge i_net_rx_clk)
	if (rx_reset)
	begin
		arp_packets_rcvd <= 0;
		arp_active <= 0;
	end else if (arp_match && !arp_active)
	begin
		arp_packets_rcvd <= arp_packets_rcvd + 1;
		arp_active <= 1;
	end else if (!ARPRX_VALID && !arp_match)
		arp_active <= 0;

	always @(posedge i_net_rx_clk)
	if (rx_reset)
	begin
		icmp_packets_rcvd <= 0;
		icmp_active <= 0;
	end else if (icmp_match && !icmp_active)
	begin
		icmp_packets_rcvd <= icmp_packets_rcvd + 1;
		icmp_active <= 1;
	end else if (!ICMPRX_VALID && !icmp_match)
		icmp_active <= 0;


	initial	dbg_packets_rcvd = 0;
	initial	dbg_active = 0;
	always @(posedge i_net_rx_clk)
	if (rx_reset)
	begin
		dbg_packets_rcvd <= 0;
		dbg_active <= 0;
	end else if (dbg_match && !dbg_active)
	begin
		dbg_packets_rcvd <= dbg_packets_rcvd + 1;
		dbg_active <= 1;
	end else if (!DBGRX_VALID && !dbg_match)
		dbg_active <= 0;


	tfrvalue #(
		.W(4*32), .DEFAULT({(4*32){1'b0}})
	) tfr_rxcounters (
		// {{{
		.i_a_clk(i_net_rx_clk), .i_a_reset_n(!rx_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_tfrrx_ready),
			.i_a_data({ pkts_rcvd, arp_packets_rcvd,
				icmp_packets_rcvd, dbg_packets_rcvd }),
		.i_b_clk(i_clk), .i_b_reset_n(!i_reset),
		.o_b_valid(ign_tfrrx_valid), .i_b_ready(1'b1),
			.o_b_data({ wb_pkts_rcvd, wb_arp_packets_rcvd,
				wb_icmp_packets_rcvd, wb_dbg_packets_rcvd })
		// }}}
	);

	// }}}

	////
	//// Transmit (outgoming) accounting
	////
	// {{{
	initial	pkts_tx = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
		pkts_tx <= 0;
	else if (TX_VALID && TX_READY && TX_LAST && !TX_ABORT)
		pkts_tx <= pkts_tx + 1;

	initial	arp_packets_tx = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
		arp_packets_tx <= 0;
	else if (ARPS_VALID && ARPS_READY && ARPS_LAST && !ARPS_ABORT)
		arp_packets_tx <= arp_packets_tx + 1;

	initial	icmp_packets_tx = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
		icmp_packets_tx <= 0;
	else if (ICMPS_VALID && ICMPS_READY && ICMPS_LAST && !ICMPS_ABORT)
		icmp_packets_tx <= icmp_packets_tx + 1;

	initial	dbg_packets_tx = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
		dbg_packets_tx <= 0;
	else if (DBGS_VALID && DBGS_READY && DBGS_LAST && !DBGS_ABORT)
		dbg_packets_tx <= dbg_packets_tx + 1;

	initial	data_packets_tx = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
		data_packets_tx <= 0;
	else if (DATAS_VALID && DATAS_READY && DATAS_LAST && !DATAS_ABORT)
		data_packets_tx <= data_packets_tx + 1;

	initial	tx_aborts = 0;
	initial	tx_in_progress = 0;
	always @(posedge i_net_tx_clk)
	if (tx_reset)
	begin
		tx_aborts <= 0;
		tx_in_progress <= 0;
	end else begin
		if (ARPS_VALID && ARPS_READY)
			tx_in_progress[5] <= ARPS_LAST;
		if (ICMPS_VALID && ICMPS_READY)
			tx_in_progress[4] <= ICMPS_LAST;
		// tx_in_progress[3] <= 1'b0;
		if (CPUS_VALID && CPUS_READY)
			tx_in_progress[2] <= CPUS_LAST;
		if (DBGS_VALID && DBGS_READY)
			tx_in_progress[1] <= DBGS_LAST;
		if (DATAS_VALID && DATAS_READY)
			tx_in_progress[0] <= DATAS_LAST;

		if (ARPS_ABORT && (!ARPS_VALID || ARPS_READY) && tx_in_progress[5])
		begin
			tx_in_progress[5] <= 1'b0;
			// tx_aborts[31:28] <= 4'h5;
			tx_aborts[27:0] <= tx_aborts[27:0] + 1;
		end

		if (ICMPS_ABORT && (!ICMPS_VALID || ICMPS_READY) && tx_in_progress[4])
		begin
			tx_in_progress[4] <= 1'b0;
			// tx_aborts[31:28] <= 4'h4;
			tx_aborts[27:0] <= tx_aborts[27:0] + 1;
		end

		if (CPUS_ABORT && (!CPUS_VALID || CPUS_READY) && tx_in_progress[2])
		begin
			tx_in_progress[2] <= 1'b0;
			// tx_aborts[31:28] <= 4'h2;
			tx_aborts[27:0] <= tx_aborts[27:0] + 1;
		end

		if (DBGS_ABORT && (!DBGS_VALID || DBGS_READY) && tx_in_progress[1])
		begin
			tx_in_progress[1] <= 1'b0;
			// tx_aborts[31:28] <= 4'h1;
			tx_aborts[27:0] <= tx_aborts[27:0] + 1;
		end

		if (DATAS_ABORT && (!DATAS_VALID || DATAS_READY) && tx_in_progress[0])
		begin
			tx_in_progress[0] <= 1'b0;
			// tx_aborts[31:28] <= 4'h0;
			tx_aborts[27:0] <= tx_aborts[27:0] + 1;
		end
	end

	tfrvalue #(
		.W(6*32), .DEFAULT({(6*32){1'b0}})
	) tfr_txcounters (
		// {{{
		.i_a_clk(i_net_tx_clk), .i_a_reset_n(!tx_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_tfrtx_ready),
			.i_a_data({ pkts_tx, arp_packets_tx, icmp_packets_tx,
				data_packets_tx, tx_aborts, dbg_packets_tx }),
		.i_b_clk(i_clk), .i_b_reset_n(!i_reset),
		.o_b_valid(ign_tfrtx_valid), .i_b_ready(1'b1),
			.o_b_data({ wb_pkts_tx, wb_arp_packets_tx,
				wb_icmp_packets_tx,
				wb_data_packets_tx,
				wb_tx_aborts, wb_dbg_packets_tx })
		// }}}
	);

	// }}}

	////
	//// Bus handling
	////
	// {{{
	initial	{ wb_ack, ack_pipe } = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ wb_ack, ack_pipe } <= 0;
	else
		{ wb_ack, ack_pipe } <= { ack_pipe, i_wb_stb && !net_stall };

	always @(posedge i_clk)
	case(i_wb_addr)
	5'h08:  pipe_data <= { OPT_DEBUG, r_debugsel, wb_pkts_rcvd[27:0] };
	5'h09:  pipe_data <= wb_arp_packets_rcvd;
	5'h0a:  pipe_data <= wb_icmp_packets_rcvd;
	5'h0b:  pipe_data <= wb_pkts_tx;
	5'h0c:  pipe_data <= wb_arp_packets_tx;
	5'h0d:  pipe_data <= wb_icmp_packets_tx;
	5'h0e:  pipe_data <= wb_data_packets_tx;
	5'h0f:  pipe_data <= wb_tx_aborts;
	5'h10:  pipe_data <= wb_dbg_packets_rcvd;
	5'h11:  pipe_data <= wb_dbg_packets_tx;
	//
	default: pipe_data <= 0;
	endcase

	always @(posedge i_clk)
		pipe_src <= (i_wb_addr < 8) ? 0:1;

	always @(posedge i_clk)
		wb_data <= (pipe_src) ? pipe_data : net_data;

	initial	r_debugsel = 3'b101;
	always @(posedge i_clk)
	if (i_wb_stb && i_wb_we && i_wb_addr == 8 && i_wb_sel[3])
		r_debugsel <= i_wb_data[30:28];

	assign	w_debugsel = r_debugsel;

	assign	o_wb_ack = wb_ack;
	assign	o_wb_stall = net_stall; // always zero
	assign	o_wb_data  = wb_data;
	assign	net_stb = i_wb_stb && i_wb_addr[4:3] == 2'b00;
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	perf_unused;
	assign	perf_unused = &{ 1'b0, ign_tfrrx_ready, ign_tfrrx_valid,
			ign_tfrtx_ready, ign_tfrtx_valid, net_ack,
			wb_pkts_rcvd[31:28] };
	// Verilator lint_on  UNUSED
	// }}}
	// }}}
`else
	assign	net_stb = i_wb_stb;
	assign	o_wb_ack   = net_ack;
	assign	o_wb_data  = net_data;
	assign	o_wb_stall = net_stall;

	assign	w_debugsel = 3'b000;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug net selection
	// {{{

	tfrvalue #(
		.W(3)
	) tfr_rxdbgsel (
		// {{{
		.i_a_clk(i_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_tfrrxdbg_ready),
			.i_a_data(w_debugsel),
		.i_b_clk(i_net_rx_clk), .i_b_reset_n(!rx_reset),
		.o_b_valid(ign_tfrrxdbg_valid), .i_b_ready(1'b1),
			.o_b_data(n_rx_debugsel)
		// }}}
	);


	tfrvalue #(
		.W(3)
	) tfr_txdbgsel (
		// {{{
		.i_a_clk(i_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_tfrtxdbg_ready),
			.i_a_data(w_debugsel),
		.i_b_clk(i_net_tx_clk), .i_b_reset_n(!tx_reset),
		.o_b_valid(ign_tfrtxdbg_valid), .i_b_ready(1'b1),
			.o_b_data(n_tx_debugsel)
		// }}}
	);


	generate if(OPT_DEBUG == 1'b0)
	begin : GEN_RX_DEBUG
		// assign o_debug_clk = i_net_rx_clk;
		// assign o_debug     = arp_debug;
		assign o_debug_clk = i_net_rx_clk;
		assign o_debug     = rx_debug;
	end else begin : GEN_TX_DEBUG
		assign	o_debug_clk = i_net_tx_clk;
		assign	o_debug     = tx_debug;
	end endgenerate

	// 3'b000: ARP
	// 3'b001: ICMP
	// 3'b010: DATA
	// 3'b011: NET (could also be CPU)
	// 3'b100: DEBUG
	// 3'b101: SPLIT / MERGE
	// 3'b110: RAW
	// 3'b111: CORE

	always @(posedge i_net_rx_clk)
	case(n_rx_debugsel)
	3'b000: rx_debug <= rx_arp_debug;
	3'b001: rx_debug <= rx_icmp_debug;
	// 3'b010: rx_debug <= rx_data -- unused;
	// 3'b011: rx_debug <= rx_cpu; // NET / CPU, Not used yet
	3'b100: rx_debug <= dbgrx_debug;
	3'b101: rx_debug <= rx_split_debug;
	3'b110: rx_debug <= rx_raw_debug;
	3'b111: rx_debug <= (OPT_DEBUG == 1'b0) ? core_debug : 32'h0;
	default:
		rx_debug <= 32'h0;
	endcase

	always @(posedge i_net_tx_clk)
	case(n_tx_debugsel)
	3'b000: tx_debug <= tx_arp_debug;
	3'b001: tx_debug <= tx_icmp_debug;
	3'b010: tx_debug <= data_debug;
	// 3'b011: tx_debug <= cpu_debug;
	3'b100: tx_debug <= dbgtx_debug;
	3'b101: tx_debug <= tx_merge_debug;
	3'b110: tx_debug <= tx_raw_debug;
	3'b111: tx_debug <= (OPT_DEBUG == 1'b1) ? core_debug : 32'h0;
	default:
		tx_debug <= 32'h0;
	endcase
	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ core_debug_clk, core_debug,
			ign_tfrrxdbg_valid, ign_tfrrxdbg_ready,
			ign_tfrtxdbg_valid, ign_tfrtxdbg_ready,
			n_rx_debugsel, n_tx_debugsel,
			high_speed_net,
			ARPS_BYTES, ICMPS_BYTES, CPUS_BYTES, DATAS_BYTES,
				DBGS_BYTES,
			CPUBUS_BYTES[2], DBGW_BYTES[2],
			M_DBG_ABORT,	// Will always be zero
			tx_in_progress[3], rx_debug, tx_debug };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
