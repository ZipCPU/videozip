////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/enetstream.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To communicate between the Ethernet PHY, and thus to coordinate
//		(and direct/arrange for) the transmission, and receiption, of
//	packets via the Ethernet interface.
//
//
//	Using this interface requires four registers to be properly configured.
//	These are the receive and transmit control registers, as well as the
//	hardware MAC register(s).
//
//
//	To use the interface, after the system has been alive for a full
//	second, drop the reset line.  Do this by writing to the transmit
//	register a value with zero length, zero command, and the RESET bit as
//	zero.
//
//	This interface is big endian.  Therefore, the most significant byte
//	in each word will be transmitted first.  If the interface references
//	a number of octets less than a multiple of four, the least significant
//	octets in the last word will not be transmitted/were not received.
//
//	To transmit,
//		1. set the source MAC address in the two mac registers.  These
//			are persistent across packets, so once set (whether for
//			transmit or receive) they need not be set again.
//		2. Provide the packet on the S_AXI_T* interface
//	OPTIONS:
//		You can turn off the internal insertion of the hardware source
//		MAC by turning the respective bit on in the transmit command
//		register.  If you do this, half of the second word and all the
//		third word must contain the hardware MAC.  The third word must
//		contain the EtherType, both in the top and bottom sixteen bits.
//		The Fourth word will begin user data.
//
//		You can also turn off the automatic insertion of the FCS, or
//		ethernet CRC.  Doing this means that you will need to both
//		guarantee for yourself that the packet has a minimum of 64
//		bytes in length, and that the last four bytes contain the
//		CRC.
//
//	To Receive:
//		The receiver is always on.  Received packets are automatically
//		output on the M_AXIN_* interface--whether anything downstream
//		is prepared for them or not.
//
//		If a packet with a CRC (or other) error is received, the
//		M_AXIN_ABORT signal will be raised as an indication to drop the
//		packet as its still working its way downstream.
//
//	OPTIONS:
//		The same options that apply to the transmitter apply to the
//		receiver:
//
//		HWMAC.  If the hardware MAC is turned on, the receiver will
//		only accept packets to either 1) our network address, or 2)
//		a broadcast address.  Further, the first two words will be
//		adjusted to contain the source MAC and the EtherType, so that
//		the user information begins on the third word.  If this feature
//		is turned off, all packets will be received, and the first
//		three words will contain the destination and then source
//		MAC.  The fourth word will contain the EtherType in the lowest,
//		16 bits, meaning user data will begin on the fifth word.
//
//		HWCRC.  If the HWCRC is turned on, the receiver will only
//		detect packets that pass their CRC check.  Further, the packet
//		length (always in octets) will not include the CRC.  However,
//		the CRC will still be left/written to packet memory either way.
//
// Registers:
//	0	Receiver control
//		13'h0	|CRCerr|MISS|ERR|BUSY| 15'h0
//
//	1	Transmitter control
//		14'h0	|NET_RST|SW-MAC-CHK|SW-CRCn|BUSY | 14'h0
//
//	2	// MAC address (high) ??
//	3	// MAC address (low)  ??
//	4	Number of receive packets missed (buffer was full)
//	5	Number of receive packets ending in error
//	6	Number of receive packets with invalid CRCs
//	7	(Number of transmit collisions ??)
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
module	enetstream #(
		// {{{
		parameter	[47:0]	DEF_HWMAC = 48'h82_33_48_02,
		parameter	[31:0]	DEF_IPADDR= 32'hc0_a8_07_89,
		// OPT_IPADDR_CHECK: If true drop packets addressed to other IPs
		parameter	[0:0]	OPT_IPADDR_CHECK = 1'b1,
		// Select whether the outgoing debug wires are associated
		// with the receive or the transmit side of interface
		parameter	[0:0]	RXSCOPE = 1'b1,
		parameter	[0:0]	OPT_MONITOR = 1'b1
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire		S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		// Resets
		output	wire		o_tx_reset, o_rx_reset,
		output	wire	[31:0]	o_rx_my_ipaddr,
		output	wire		o_high_speed,
		input	wire	[3:0]	i_addr_switch,
		//
		// Wishbone: The network control interface
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[2:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg	[31:0]	o_wb_data,
		// }}}
		// Incoming packet interface
		// {{{
		input	wire		S_AXI_TVALID,
		output	wire		S_AXI_TREADY,
		input	wire	[7:0]	S_AXI_TDATA,
		// input	wire		S_AXI_TLAST,
		// }}}
		// Outgoing packet interface
		// {{{
		output	wire		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	wire	[7:0]	M_AXIN_DATA,
		output	wire		M_AXIN_LAST,
		output	wire		M_AXIN_ABORT,
		// }}}
		// Monitor of the outgoing packet interface
		// {{{
		output	wire		MON_VALID,
		input	wire		MON_READY,
		output	wire	[7:0]	MON_DATA,
		output	wire		MON_LAST,
		output	wire		MON_ABORT,
		// }}}
		// PHY interface
		// {{{
		// Verilator lint_off SYNCASYNCNET
		output	reg		o_net_reset_n,
		// Verilator lint_on  SYNCASYNCNET
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
		// Addresses
		output	wire	[47:0]	o_hw_mac,
		output	wire	[31:0]	o_ipaddr,
		//
		output	wire		o_debug_clk,
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Signal declarations
	// {{{
	wire	i_wb_clk = S_AXI_ACLK;
	wire	i_reset  = !S_AXI_ARESETN;

	localparam	[2:0]	ADR_RXCTRL  = 3'b000,
				ADR_TXCTRL  = 3'b001,
				ADR_HWMACHI = 3'b010,
				ADR_HWMACLO = 3'b011,
				ADR_IPADDR  = 3'b100,
				ADR_RXMISS  = 3'b101,
				ADR_RXERR   = 3'b110,
				ADR_CRCFAIL = 3'b111;

	// (* ASYNC_REG = "TRUE" *) reg	rx_broadcast;
	// (* ASYNC_REG = "TRUE" *) reg	[(MAW+1):0]	rx_len;

	reg		config_hw_crc, config_hw_mac, config_hw_ip_check;
	// reg		rx_crcerr, rx_err, rx_miss;
	reg		rx_err_stb, rx_miss_stb, rx_crc_stb;

	reg	[47:0]	hw_mac;
	reg	[31:0]	my_ipaddr;

	wire	[1:0]	tx_spd;

	wire		rx_full_duplex, rx_link_up;
	wire	[1:0]	rx_link_spd;

	wire	[31:0]	w_tx_ctrl;
	wire	[31:0]	w_rx_ctrl;
	reg	[31:0]	counter_rx_miss, counter_rx_err, counter_rx_crc;

	reg		tx_ready;
	reg	[3:0]	tx_recycle;

	reg		wr_ctrl;
	reg	[2:0]	wr_addr;
	reg	[31:0]	wr_data;
	reg	[3:0]	wr_sel;

	reg		ip_switch_control, mac_switch_control;

	// Receive registers and signals
	// {{{
`ifdef	VERILATOR
	// A half millisecond--to spare simulation cycles
	localparam	ONE_SECOND =      62_500;
`else
	localparam	ONE_SECOND = 125_000_000;
`endif
	localparam	RESET_BITS = $clog2(ONE_SECOND+1);
	localparam	CKCHECK_BITS = 6;

	reg		n_rx_reset;
	(* ASYNC_REG = "TRUE" *) reg n_rx_config_hw_mac, n_rx_config_hw_crc,
			n_rx_config_ip_check;
	reg		n_rx_net_err;
	wire		w_npre,  w_rxmin,  w_rxcrc,  w_rxip,  w_rxmac;
	wire	[7:0]	w_npred, w_rxmind, w_rxcrcd, w_rxipd, w_rxmacd;
	wire		w_minerr, w_rxcrcerr, w_macerr, w_broadcast, w_iperr;
	reg		n_rx_crcerr,
			n_rx_err, n_rx_miss;
			// n_rx_broadcast
	reg		n_rx_full_duplex, n_rx_link_up;
	reg	[1:0]	n_rx_link_spd;

	reg	[RESET_BITS-1:0]	net_reset_timer;
	reg	[CKCHECK_BITS:0]	rxclk_check, txclk_check;
	reg				pre_rx_reset, pre_tx_reset;
	(* ASYNC_REG *)	reg	[1:0]	preq_rx_reset, preq_tx_reset;
	(* ASYNC_REG *) reg	[1:0]	q_tx_reset, q_rx_reset;



	reg		n_tx_reset;
	reg	[1:0]	n_tx_spd;
	wire	[1:0]	n_tx_link_spd_raw;
	wire		tx_ce;
	wire		w_macen, w_paden, w_txcrcen, w_txprev;
	wire	[7:0]	w_macd,  w_padd,  w_txcrcd,  w_txpred;

	(* ASYNC_REG = "TRUE" *) reg	n_tx_config_hw_mac, n_tx_config_hw_crc;
	wire	n_tx_config_hw_preamble;
	reg	[3:0]	rx_err_pipe, rx_miss_pipe, rx_crc_pipe;

	wire		ign_rxspd_tfr_ready, ign_rxspd_tfr_valid;
	wire		ign_rxipaddr_ready, ign_rxipaddr_valid;
	wire	[31:0]	n_rx_my_ipaddr;

	// }}}

	initial	config_hw_crc = 1;
	initial	config_hw_mac = 1;
	initial	config_hw_ip_check = 1;
	//
	// initial	rx_crcerr = 1'b0;
	// initial	rx_err    = 1'b0;
	// initial	rx_miss   = 1'b0;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// The control interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	initial	wr_ctrl = 0;

	// wr_ctrl, wr_addr, wr_data, wr_sel
	// {{{
	always @(posedge i_wb_clk)
	begin
		wr_ctrl <=(i_wb_stb)&&(i_wb_we);
		wr_addr <= i_wb_addr[2:0];
		wr_data <= i_wb_data;
		wr_sel  <= i_wb_sel;

		if (i_reset)
			wr_ctrl <= 1'b0;
	end
	// }}}

	initial	hw_mac    = DEF_HWMAC;
	initial	my_ipaddr = DEF_IPADDR;
	initial	ip_switch_control  = 1'b1;
	initial	mac_switch_control = 1'b1;
	always @(posedge i_wb_clk)
	begin
		////////////////////////////////////////////////////////////////
		//
		// RX Control
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// Important bits: SOFT-RESET, and ACTIVE
		// }}}
		////////////////////////////////////////////////////////////////
		//
		// TX Control
		// {{{
		////////////////////////////////////////////////////////////////
		//
		//

		// Important bits: SOFT-RESET, TX-ACTIVE, SPEED
		//	(OPT HWMAC, OPT_CRC, OPT_HWIPCK)
		/*
		if ((wr_ctrl)&&(wr_addr==3'b001))
		begin // TX command register

			// Set the transmit speed
			if (wr_sel[3] && wr_data[24])
			begin
				tx_spd <= wr_data[31:30];
			end

			// Reset bit must be held down to be valid
			if (wr_sel[2])
			begin
				config_hw_ip_check <= (!wr_data[18]);
				o_net_reset_n <= (!wr_data[17]);
				config_hw_mac <= (!wr_data[16]);
			end

			if (wr_sel[1])
			begin
				config_hw_crc <= (!wr_data[15]);
			end
		end
		*/
		// }}}
		// Set the hardware MAC
		// {{{
		if (mac_switch_control)
			hw_mac <= DEF_HWMAC ^ { {(44){1'b0}}, i_addr_switch };
		if ((wr_ctrl)&&(wr_addr==ADR_HWMACHI))
		begin
			if (wr_sel[1])
				hw_mac[47:40] <= wr_data[15:8];
			if (wr_sel[0])
				hw_mac[39:32] <= wr_data[7:0];
			if (|wr_sel[1:0])
				mac_switch_control <= 1'b0;
		end
		if ((wr_ctrl)&&(wr_addr==ADR_HWMACLO))
		begin
			if (wr_sel[3])
				hw_mac[31:24] <= wr_data[31:24];
			if (wr_sel[2])
				hw_mac[23:16] <= wr_data[23:16];
			if (wr_sel[1])
				hw_mac[15: 8] <= wr_data[15: 8];
			if (wr_sel[0])
				hw_mac[ 7: 0] <= wr_data[ 7: 0];
			if (|wr_sel)
				mac_switch_control <= 1'b0;
		end
		// }}}
		// Set the hardware IP address
		// {{{
		if (ip_switch_control)
			my_ipaddr<= DEF_IPADDR^ { {(26){1'b0}},
							i_addr_switch, 2'b00 };
		if ((wr_ctrl)&&(wr_addr==ADR_IPADDR))
		begin
			if (wr_sel[3])
				my_ipaddr[31:24] <= wr_data[31:24];
			if (wr_sel[2])
				my_ipaddr[23:16] <= wr_data[23:16];
			if (wr_sel[1])
				my_ipaddr[15: 8] <= wr_data[15: 8];
			if (wr_sel[0])
				my_ipaddr[ 7: 0] <= wr_data[ 7: 0];
			if (|wr_sel)
				ip_switch_control <= 1'b0;
		end
		// }}}

		if (!S_AXI_ARESETN)
		begin
			hw_mac    <= DEF_HWMAC;
			my_ipaddr <= DEF_IPADDR;
		end
	end

	assign	o_hw_mac = hw_mac;
	assign	o_ipaddr = my_ipaddr;

	// w_rx_ctrl
	// {{{
	assign	w_rx_ctrl = {
			rx_link_spd, !rx_full_duplex, !rx_link_up,	// 4bits
			rxclk_check[CKCHECK_BITS], 1'h0,		// 4bits
			i_addr_switch, ip_switch_control, mac_switch_control,
			1'b0, // (rx_broadcast), // 1-bit
			3'h0, // rx_crcerr, rx_err, rx_miss,	// 3-bits
			// 16-bits follow
			16'b0 };
	// }}}

	// n_tx_spd
	//  {{{
	// Verilator lint_off UNUSED
	wire	ign_wbspd_ready, ign_txspd_valid;
	// Verilator lint_on  UNUSED

	tfrvalue #(	// WB CLK -> TX CLK
		// {{{
		.W(2)
		// }}}
	) tfrtxspd (
		// {{{
		.i_a_clk(i_wb_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_wbspd_ready),
			.i_a_data(rx_link_spd),
		.i_b_clk(i_net_tx_clk), .i_b_reset_n(!n_tx_reset),
		.o_b_valid(ign_txspd_valid), .i_b_ready(1'b1),
			.o_b_data(n_tx_link_spd_raw)
		// }}}
	);

	/*
	wire		ign_txtfr_ready, ign_txtfr_valid;

	tfrvalue #(	// TX CLK -> WB CLK	(No longer used)
		// {{{
		.W(2)
		// }}}
	) tfrtxspd (
		// {{{
		.i_a_clk(i_net_tx_clk), .i_a_reset_n(!n_tx_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_txtfr_ready),
		.i_a_data(n_tx_spd),
		.i_b_clk(i_wb_clk), .i_b_reset_n(!i_reset),
		.o_b_valid(ign_txtfr_valid), .i_b_ready(1'b1),
		.o_b_data(tx_spd)
		// }}}
	);
	*/

	assign	tx_spd = rx_link_spd;

	initial	n_tx_spd = 2'b10;
	always @(posedge i_net_tx_clk)
	if (n_tx_reset)
		n_tx_spd <= 2'b10;
	else if (!S_AXI_TVALID)
		n_tx_spd <= n_tx_link_spd_raw;
	// }}}

	// w_tx_ctrl
	// {{{
	assign	w_tx_ctrl = { tx_spd, 5'h0, ((RXSCOPE) ? 1'b0:1'b1),	// 8b
			txclk_check[CKCHECK_BITS],			// 4b
				1'b0, ip_switch_control,
				mac_switch_control,
			!config_hw_ip_check, !o_net_reset_n,!config_hw_mac,
				!config_hw_crc,				// 4b
			16'h00 };
	// }}}


	// Reads from the bus ... always done, regardless of i_wb_we
	always @(posedge i_wb_clk)
	casez(i_wb_addr[2:0])
	ADR_RXCTRL:  o_wb_data <= w_rx_ctrl;
	ADR_TXCTRL:  o_wb_data <= w_tx_ctrl;
	ADR_HWMACHI: o_wb_data <= { 2'b00,
				ip_switch_control, mac_switch_control,
				i_addr_switch,
				8'h00, hw_mac[47:32] };
	ADR_HWMACLO: o_wb_data <= hw_mac[31:0];
	ADR_IPADDR:  o_wb_data <= my_ipaddr;
	ADR_RXMISS:  o_wb_data <= counter_rx_miss;
	ADR_RXERR:   o_wb_data <= counter_rx_err;
	ADR_CRCFAIL: o_wb_data <= counter_rx_crc;
	default: o_wb_data <= 32'h00;
	endcase

	initial	o_wb_ack = 1'b0;
	always @(posedge i_wb_clk)
		o_wb_ack <= (i_wb_stb)&&(!i_reset);

	assign	o_wb_stall = 1'b0;

	assign	o_high_speed = (tx_spd == 2'b00);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset crosses clock domains
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_net_reset_n
	// {{{
	// Generate a PHY reset--releases only a full second after the bus
	// reset releases

	// rxclk_check: Make sure the RX clock is ticking
	// {{{
	always @(posedge i_net_rx_clk or negedge S_AXI_ARESETN)
	if (!S_AXI_ARESETN)
		{ pre_rx_reset, preq_rx_reset } <= -1;
	else
		{ pre_rx_reset, preq_rx_reset } <= { preq_rx_reset, 1'b0 };

	always @(posedge i_net_rx_clk or posedge pre_rx_reset)
	if (pre_rx_reset)
		rxclk_check <= 0;
	else if (!rxclk_check[CKCHECK_BITS-1])
		rxclk_check <= rxclk_check + 1;
	// }}}

	// txclk_check: Make sure the TX clock is ticking
	// {{{
	always @(posedge i_net_tx_clk or negedge S_AXI_ARESETN)
	if (!S_AXI_ARESETN)
		{ pre_tx_reset, preq_tx_reset } <= -1;
	else
		{ pre_tx_reset, preq_tx_reset } <= { preq_tx_reset, 1'b0 };

	always @(posedge i_net_rx_clk or posedge pre_tx_reset)
	if (pre_tx_reset)
		txclk_check <= 0;
	else if (!txclk_check[CKCHECK_BITS-1])
		txclk_check <= txclk_check + 1;
	// }}}

	// o_net_reset_n, net_reset_timer
	// {{{
	initial	o_net_reset_n   = 1'b0;
	initial	net_reset_timer = ONE_SECOND;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		o_net_reset_n <= 1'b0;
		net_reset_timer   <= ONE_SECOND;
	end else begin
		if (net_reset_timer > 0)
		begin
			// Insist both TX and RX clocks exist and are active
			// before allowing the reset to complete
			/*
			// This makes no sense, if the RX clock will be held
			// constant as long as reset is asserted ...
			//
			if (net_reset_timer[RESET_BITS-1:RESET_BITS-3] == 0)
			begin
				if (txclk_check[CKCHECK_BITS-1]
						&& rxclk_check[CKCHECK_BITS-1])
					net_reset_timer <= net_reset_timer - 1;
			end else
			*/
				net_reset_timer <= net_reset_timer - 1;
		end

		o_net_reset_n <= (net_reset_timer <= 1);

		if (wr_ctrl && wr_sel[2] && wr_addr == 3'b001 && wr_data[17])
		begin // TX command register
			o_net_reset_n <= 0;
			net_reset_timer <= ONE_SECOND;
		end
	end
	// }}}
	// }}}

	// o_rx_reset, n_rx_reset, q_rx_reset
	// {{{
	initial	{ n_rx_reset, q_rx_reset } = -1;
	always @(posedge i_net_rx_clk or negedge o_net_reset_n)
	if (!o_net_reset_n)
		{ n_rx_reset, q_rx_reset } <= -1;
	else
		{ n_rx_reset, q_rx_reset } <= { q_rx_reset, 1'b0 };

	assign	o_rx_reset = n_rx_reset;
	// }}}

	initial	{ n_tx_reset, q_tx_reset } = -1;
	always @(posedge i_net_tx_clk or negedge o_net_reset_n)
	if (!o_net_reset_n)
		{ n_tx_reset, q_tx_reset } <= -1;
	else
		{ n_tx_reset, q_tx_reset } <= { q_tx_reset, 1'b0 };

	assign	o_tx_reset = n_tx_reset;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Transmitter code
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_net_tx_clk)
	if (!S_AXI_TVALID)
	begin
		n_tx_config_hw_mac <= config_hw_mac;
		n_tx_config_hw_crc <= config_hw_crc;
	end

	// Accept the stream input
	// {{{
	assign	S_AXI_TREADY = tx_ce && tx_ready;

	// tx_ready, tx_recycle
	// {{{
	// Force idle cycles between packets, up to 15 bytes
	initial	tx_ready = 0;
	initial	tx_recycle = -1;
	always @(posedge i_net_tx_clk)
	if (o_tx_reset)
	begin
		tx_ready   <= 0;
		tx_recycle <= -1;
	end else if (S_AXI_TVALID && tx_ready)
	begin
		tx_recycle <= -1;
	end else if (!o_net_tx_ctl)
	begin
		if (tx_recycle > 1)
		begin
			tx_recycle <= tx_recycle - 1;
			tx_ready <= 0;
		end else begin
			tx_recycle <= 0;
			tx_ready <= 1;
		end
	end else begin
		tx_ready <= 0;
		tx_recycle <= -1;
	end
	// }}}
	// }}}

	assign	n_tx_config_hw_preamble = 1'b1;

	// TX add MAC address
	// {{{
`ifndef	TX_BYPASS_HW_MAC
	addemac
	txmaci(
		// {{{
		.i_clk(i_net_tx_clk), .i_reset(n_tx_reset),
		.i_ce(tx_ce), .i_en(n_tx_config_hw_mac),
		.i_hw_mac(hw_mac),
		.i_v(S_AXI_TVALID && S_AXI_TREADY), .i_byte(S_AXI_TDATA),
		.o_v(w_macen), .o_byte(w_macd)
		// }}}
	);
`else
	assign	w_macen = S_AXI_TVALID && S_AXI_TREADY;
	assign	w_macd  = S_AXI_TDATA;
`endif
	// }}}

	// Pad transmit packets to a minimum length
	// {{{
`ifndef	TX_BYPASS_PADDING
	addepad	txpadi(i_net_tx_clk, (n_tx_reset), tx_ce,
				w_macen, w_macd, w_paden, w_padd);
`else
	assign	w_paden = w_macen;
	assign	w_padd  = w_macd;
`endif
	// }}}

	// Add a CRC to all transmit packets
	// {{{
`ifndef	TX_BYPASS_HW_CRC
	addecrc	txcrci(i_net_tx_clk, (n_tx_reset), tx_ce,
				n_tx_config_hw_crc,
				w_paden, w_padd, w_txcrcen, w_txcrcd);
`else
	assign	w_txcrcen = w_macen;
	assign	w_txcrcd  = w_macd;
`endif
	// }}}

	// Add the ethernet preamble
	// {{{
	addepreamble txprei(i_net_tx_clk, n_tx_reset, tx_ce,
				n_tx_config_hw_preamble,
				w_txcrcen, w_txcrcd, w_txprev, w_txpred);
	// }}}

	// Drive the final outgoing I/O wires, and the tx_ce signal
	// {{{
	// txespeed helps us support 10Mbps, 100Mbps, and 1Gbps
	// without changing clock speed
	//
	txespeed
	txspdi(
		// {{{
		.i_clk(i_net_tx_clk), .i_reset(n_tx_reset), .i_spd(n_tx_spd),
		.i_v(w_txprev), .i_d(w_txpred),
		.o_v(o_net_tx_ctl), .o_d(o_net_txd),
		.o_ce(tx_ce), .o_ck(o_net_tx_ck)
		// }}}
	);
	// }}}

	generate if (OPT_MONITOR)
	begin : GEN_MONITOR
		wire		w_xpre,  w_xmin,  w_xcrc,  w_txip,  w_txmac;
		wire	[7:0]	w_xpred, w_xmind, w_xcrcd, w_txipd, w_txmacd;
		wire		w_txminerr, w_xcrcerr;

		// Hardware preamble detection and removal
		// {{{
		rxepreambl
		mon_pre(i_net_tx_clk, n_tx_reset, 1'b1, 1'b1,
			o_net_tx_ctl, o_net_txd, w_xpre, w_xpred);
		// }}}

		// w_minerr: Minimum packet length checking
		// {{{
		// Insist on a minimum of 64-byte packets
		rxemin
		min_min(
			// {{{
			.i_clk(i_net_tx_clk),
			.i_reset(n_tx_reset),
			.i_en(1'b1),
			.i_ce(1'b1),
			.i_v(w_xpre),
			.o_err(w_txminerr)
			// }}}
		);

		assign	w_xmin = w_xpre;
		assign	w_xmind= w_xpred;
		// }}}

		// w_xcrcerr: RX CRC checking
		// {{{
		rxecrc
		mon_xcrc(
			// {{{
			.i_clk(i_net_tx_clk), .i_reset(n_tx_reset),
				.i_ce(1'b1), .i_en(1'b1),
				.i_v(w_xmin), .i_d(w_xmind),
				.o_v(w_xcrc), .o_d(w_xcrcd),
				.o_err(w_xcrcerr)
			// }}}
		);
		// }}}

		assign	w_txip  = w_xcrc;
		assign	w_txipd = w_xcrcd;

		assign	w_txmac  = w_txip;
		assign	w_txmacd = w_txipd;

		// MON_*
		// {{{
		rxepacket
		mon_tx2pkt (
			// {{{
			.i_clk(i_net_tx_clk),
			.i_reset(n_tx_reset),
			.i_abort(w_xcrcerr || w_txminerr),
			.i_v(w_txmac), .i_d(w_txmacd),
				.i_not_done(w_xpre || w_xmin || w_xcrc),
			.M_AXIN_VALID(MON_VALID),
			.M_AXIN_READY(MON_READY),
			.M_AXIN_DATA( MON_DATA),
			.M_AXIN_LAST( MON_LAST),
			.M_AXIN_ABORT(MON_ABORT)
			// }}}
		);
		// }}}

	end else begin : NO_MONITOR
		assign	MON_VALID = 1'b0;
		assign	MON_DATA  = 8'h0;

		// Verilator lint_off UNUSED
		wire	unused_monitor;
		assign	unused_monitor = &{ 1'b0, MON_READY };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Receiver code
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	tfrvalue #(	// WB-CLK -> RX CLK
		// {{{
		.W(32), .DEFAULT(DEF_IPADDR)
		// }}}
	) tfr_rxipaddr (
		// {{{
		.i_a_clk(i_wb_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_rxipaddr_ready),
		.i_a_data(my_ipaddr),
		.i_b_clk(i_net_rx_clk), .i_b_reset_n(!n_rx_reset),
		.o_b_valid(ign_rxipaddr_valid), .i_b_ready(1'b1),
		.o_b_data(n_rx_my_ipaddr)
		// }}}
	);

	assign	o_rx_my_ipaddr = n_rx_my_ipaddr;

	// Hardware preamble detection and removal
	// {{{
`ifndef	RX_BYPASS_HW_PREAMBLE
	rxepreambl rxprei(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)), 1'b1, 1'b1,
			i_net_rx_dv, i_net_rxd, w_npre, w_npred);
`else
	assign	w_npre  = i_net_rx_ctl;
	assign	w_npred = 1'b0;
`endif
	// }}}

	// w_minerr: Minimum packet length checking
	// {{{
`ifndef	RX_BYPASS_HW_MINLENGTH
	// Insist on a minimum of 64-byte packets
	rxemin
	rxmini(
		// {{{
		.i_clk(i_net_rx_clk),
		.i_reset((n_rx_reset)||(n_rx_net_err)),
		.i_en(1'b1),
		.i_ce(1'b1),
		.i_v(w_npre),
		.o_err(w_minerr)
		// }}}
	);
`else
	assign	w_minerr= 1'b0;
`endif
	assign	w_rxmin = w_npre;
	assign	w_rxmind= w_npred;
	// }}}

	// w_rxcrcerr: RX CRC checking
	// {{{
`ifndef	RX_BYPASS_HW_CRC
	rxecrc
	rxcrci(
		// {{{
		.i_clk(i_net_rx_clk), .i_reset((n_rx_reset)||(n_rx_net_err)),
			.i_ce(1'b1), .i_en(n_rx_config_hw_crc),
			.i_v(w_rxmin), .i_d(w_rxmind),
			.o_v(w_rxcrc), .o_d(w_rxcrcd), .o_err(w_rxcrcerr)
		// }}}
	);
`else
	assign	w_rxcrc   = w_rxmin;
	assign	w_rxcrcd  = w_rxmind;
	assign	w_rxcrcerr= 1'b0;
`endif
	// }}}

	// w_iperr: Check the IP header, raise w_iperr on failures, trim ip pkts
	// {{{
`define	RX_HW_IPCHECK
`ifdef	RX_HW_IPCHECK
	// Check: if this packet is an IP packet, is the IP header checksum
	// valid?  Does the IP address match?
	rxeipchk #(
		.OPT_IPADDR_CHECK(OPT_IPADDR_CHECK)
	) rxipci(
		.i_clk(i_net_rx_clk), .i_reset((n_rx_reset)||(n_rx_net_err)),
			.i_ce(1'b1), .i_en(n_rx_config_ip_check),
			.i_my_ipaddr(n_rx_my_ipaddr),
			.i_v(w_rxcrc), .i_d(w_rxcrcd),
			.o_v(w_rxip), .o_d(w_rxipd), .o_err(w_iperr)
	);
`else
	assign	w_rxip  = w_rxcrc;
	assign	w_rxipd = w_rxcrcd;
	assign	w_iperr = 1'b0;
`endif
	// }}}

	// w_broadcast, w_macerr: Check if this packet is for me
	// {{{
	// Strip the H/W MAC address if so
`ifndef	RX_BYPASS_HW_RMMAC
	rxehwmac
	rxmaci(
		// {{{
		.i_clk(i_net_rx_clk), .i_reset((n_rx_reset)||(n_rx_net_err)),
			.i_ce(1'b1), .i_en(n_rx_config_hw_mac),.i_hwmac(hw_mac),
			.i_v(w_rxip),  .i_d(w_rxipd),
			.o_v(w_rxmac), .o_d(w_rxmacd),
			.o_err(w_macerr), .o_broadcast(w_broadcast)
		// }}}
	);
`else
	assign	w_rxmac  = w_rxip;
	assign	w_rxmacd = w_rxipd;
`endif
	// }}}

	// M_AXIN_*
	// {{{
	rxepacket
	rx2pkt (
		// {{{
		.i_clk(i_net_rx_clk),
		.i_reset(n_rx_reset),
		.i_abort(n_rx_net_err || w_rxcrcerr || w_minerr || w_iperr),
		.i_v(w_rxmac), .i_d(w_rxmacd),
			.i_not_done(w_npre || w_rxmin || w_rxcrc),
		.M_AXIN_VALID(M_AXIN_VALID),
		.M_AXIN_READY(M_AXIN_READY),
		.M_AXIN_DATA(M_AXIN_DATA),
		.M_AXIN_LAST(M_AXIN_LAST),
		.M_AXIN_ABORT(M_AXIN_ABORT)
		// }}}
	);
	// }}}

	initial	n_rx_miss  = 1'b0;
	always @(posedge i_net_rx_clk)
	begin
		// n_rx_net_err goes true as soon as an error is detected,
		// and stays true as long as valid data is coming in
		if ((w_minerr)||(w_macerr)||(w_rxcrcerr)||(w_iperr))
			n_rx_net_err <= 1'b1;
		else if (!i_net_rx_dv)
			n_rx_net_err <= 1'b0;

		// Oops ... we missed a packet
		n_rx_miss <= M_AXIN_ABORT;

		n_rx_crcerr <= (w_rxcrcerr)&&(!n_rx_net_err);
		n_rx_err    <= w_minerr;

		if (!i_net_rx_dv && !i_net_rx_err)
		begin
			n_rx_link_up     <= i_net_rxd[0];
			n_rx_full_duplex <= i_net_rxd[3];
			case(i_net_rxd[2:1])
			2'b00: n_rx_link_spd <= 2'b10;	// 10M
			2'b01: n_rx_link_spd <= 2'b01;	// 100M
			default: n_rx_link_spd <= 2'b00;	// Gb
			endcase
		end

		if (!i_net_rx_dv)
		begin
			n_rx_config_hw_mac   <= config_hw_mac;
			n_rx_config_hw_crc   <= config_hw_crc;
			n_rx_config_ip_check <= config_hw_ip_check;
		end
	end

	tfrvalue #(	// RX-CLK -> WB-CLK
		.W(4)
	) tfrrxspd(
		// {{{
		.i_a_clk(i_net_rx_clk), .i_a_reset_n(!i_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_rxspd_tfr_ready),
		.i_a_data({ n_rx_full_duplex, n_rx_link_spd, n_rx_link_up }),
		.i_b_clk(i_wb_clk), .i_b_reset_n(!n_rx_reset),
		.o_b_valid(ign_rxspd_tfr_valid),
		.i_b_ready(1'b1),
		.o_b_data({ rx_full_duplex, rx_link_spd, rx_link_up })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Performance counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial { rx_err_pipe, rx_miss_pipe, rx_crc_pipe } = 0;
	initial	{ rx_err_stb, rx_miss_stb, rx_crc_stb } = 0;
	always @(posedge i_wb_clk)
	if (i_reset)
	begin
		{ rx_err_pipe, rx_miss_pipe, rx_crc_pipe } <= 0;
		{ rx_err_stb, rx_miss_stb, rx_crc_stb } <= 0;
	end else begin
		rx_err_pipe  <= { rx_err_pipe[2:0],  n_rx_err };
		rx_miss_pipe <= { rx_miss_pipe[2:0], n_rx_miss };
		rx_crc_pipe  <= { rx_crc_pipe[2:0],  n_rx_crcerr };

		rx_err_stb  <= (rx_err_pipe[3:2]  == 2'b01);
		rx_miss_stb <= (rx_miss_pipe[3:2] == 2'b01);
		rx_crc_stb  <= (rx_crc_pipe[3:2]  == 2'b01);
	end

	// counter_rx_miss: the RX miss counter
	// {{{
	initial	counter_rx_miss = 0;
	always @(posedge i_wb_clk)
	if (!o_net_reset_n)
		counter_rx_miss <= 32'h0;
	else if (rx_miss_stb)
		counter_rx_miss <= counter_rx_miss + 32'h1;
	// }}}

	// counter_rx_err
	// {{{
	initial	counter_rx_err = 0;
	always @(posedge i_wb_clk)
	if (!o_net_reset_n)
		counter_rx_err <= 32'h0;
	else if (rx_err_stb)
		counter_rx_err <= counter_rx_err + 32'h1;
	// }}}

	// counter_rx_crc
	// {{{
	initial	counter_rx_crc = 0;
	always @(posedge i_wb_clk)
	if (!o_net_reset_n)
		counter_rx_crc <= 32'h0;
	else if (rx_crc_stb)
		counter_rx_crc <= counter_rx_crc + 32'h1;
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Debug scope(s)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (RXSCOPE)
	begin : RXSCOPE_DEF
		// {{{
		reg	rx_trigger, rx_last_dv, rx_dvalid;

		assign	o_debug_clk = i_net_rx_clk;

		always @(*)
			rx_dvalid = i_net_rx_dv;

		initial	rx_last_dv = 0;
		always @(posedge i_net_rx_clk)
			rx_last_dv <= rx_dvalid;

		initial	rx_trigger = 0;
		always @(posedge i_net_rx_clk)
			rx_trigger <= rx_dvalid && !rx_last_dv;

		assign	o_debug = {
			// Signals, and Potential errors
			rx_trigger, 1'b0, w_macerr, w_broadcast,
			1'b0, n_rx_miss, n_rx_net_err, 1'b0, 1'b0, // 9-bits
			// Memory stage, 1-bits
			1'b0,
			//
			//
			// Preamble stage, 1-bits
			w_npre, // w_npred,
			// Min Packet, 1 bit
			w_rxmin, // w_rxmind,

			// RXCRC, 10 bits
			w_rxcrc, w_rxcrcd, w_rxcrcerr,
			// // H/W MAC processing - 1-bits
			w_rxmac, // w_rxmacd,
			//
			i_net_rx_dv, i_net_rxd };		// 9 bits
		// }}}
	end else begin : TXSCOPE_DEF
		// {{{
		assign	o_debug_clk = i_net_tx_clk;

		assign	o_debug = {
			// 3 bits
			3'b0,
			// 9 bits
			S_AXI_TVALID && S_AXI_TREADY, S_AXI_TDATA,
			// 2 bits
			w_macen, w_paden,
			// 9-bits
			w_txcrcen, w_txcrcd,
			// 9 bits
			o_net_tx_ctl, o_net_txd
		};
		// }}}
	end endgenerate
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	bus_unused;
	assign	bus_unused = &{ 1'b0, i_wb_cyc, w_broadcast, n_rx_crcerr,
				n_rx_err, n_rx_miss,
			// ign_txtfr_ready, ign_txtfr_valid,
			ign_rxspd_tfr_ready, ign_rxspd_tfr_valid,
			ign_rxipaddr_ready, ign_rxipaddr_valid };
	// verilator lint_on  UNUSED
	// }}}
endmodule
