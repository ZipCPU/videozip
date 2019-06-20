////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	enetpackets.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
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
//		2. Fill the packet buffer with your packet.  In general, the
//			first 32-bit word must contain the hardware MAC address
//			of your destination, spilling into the 16-bits of the
//			next word.  The bottom 16-bits of that second word
//			must also contain the EtherType (0x0800 for IP,
//			0x0806 for ARP, etc.)  The third word will begin your
//			user data.
//		3. Write a 0x4000 plus the number of bytes in your buffer to
//			the transmit command register.  If your packet is less
//			than 64 bytes, it will automatically be paddedd to 64
//			bytes before being sent.
//		4. Once complete, the controller will raise an interrupt
//			line to note that the interface is idle.
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
//		The receiver is always on.  Receiving is really just a matter
//		of pulling the received packet from the interface, and resetting
//		the interface for the next packet.
//
//		If the VALID bit is set, the receive interface has a valid
//		packet within it.  Write a zero to this bit to reset the
//		interface to accept the next packet.
//
//		If a packet with a CRC error is received, the CRC error bit
//		will be set.  Likewise if a packet has been missed, usually 
//		because the buffer was full when it started, the miss bit
//		will be set.  Finally, if an error occurrs while receiving
//		a packet, the error bit will be set.  These bits may be cleared
//		by writing a one to each of them--something that may be done
//		when clearing the interface for the next packet.
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
//		13'h0	|CRCerr|MISS|ERR|BUSY|VALID |14-bit length (in octets)|
//
//	1	Transmitter control
//		14'h0	|NET_RST|SW-MAC-CHK|SW-CRCn|BUSY/CMD | 14 bit length(in octets)|
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
//
// Copyright (C) 2016-2019, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
`default_nettype	none
//
module	enetpackets(i_wb_clk, i_reset,
	i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
		o_wb_ack, o_wb_stall, o_wb_data,
	//
	o_net_reset_n, 
	i_net_rx_clk, i_net_rx_dv, i_net_rx_err, i_net_rxd,
	i_net_tx_clk, o_net_tx_ck, o_net_tx_ctl, o_net_txd,
	//
	o_rx_int, o_tx_int,
	//
	o_debug_clk, o_debug
	);
	// The memory address width controls how many addresses we present
	// to the outside world.  As an example, for a MEMORY_ADDRESS_WIDTH
	// of 12, we present 2^12 octets per packet in our memory interface,
	// also known as 4kB of data in each of the RX and TX channels.  This
	// effectively defines the maximum packet size as well.
	parameter	MEMORY_ADDRESS_WIDTH = 12; // Log_2 octet width:11..14
	//
	// MAW is roughly 
	localparam	MAW =((MEMORY_ADDRESS_WIDTH>14)? 14: // width of words
			((MEMORY_ADDRESS_WIDTH<11)? 11:MEMORY_ADDRESS_WIDTH))-2;
	//
	// Select whether the outgoing debug wires are associated with the
	// receive or the transmit side of interface
	localparam	[0:0]	RXSCOPE = 1'b0;

	input	wire		i_wb_clk, i_reset;
	//
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(MAW+1):0]	i_wb_addr; // 1-bit for ctrl/data, 1 for tx/rx
	input	wire	[31:0]		i_wb_data;
	input	wire	[3:0]		i_wb_sel;
	//
	output	reg		o_wb_ack;
	output	wire		o_wb_stall;
	output	reg	[31:0]	o_wb_data;
	//
	output	reg		o_net_reset_n;
	//
	input	wire		i_net_rx_clk, i_net_rx_dv, i_net_rx_err;
	input	wire	[7:0]	i_net_rxd;
	//
	input	wire		i_net_tx_clk;
	output	wire	[1:0]	o_net_tx_ck;
	output	wire		o_net_tx_ctl;
	output	wire	[7:0]	o_net_txd;
	//
	output	wire		o_rx_int, o_tx_int;
	//
	output	wire		o_debug_clk;
	output	wire	[31:0]	o_debug;

	reg		wr_ctrl;
	reg	[2:0]	wr_addr;
	reg	[31:0]	wr_data;
	reg	[3:0]	wr_sel;
	always @(posedge i_wb_clk)
	begin
		wr_ctrl<=((i_wb_stb)&&(i_wb_we)
				&&(i_wb_addr[(MAW+1):MAW] == 2'b00));
		wr_addr <= i_wb_addr[2:0];
		wr_data <= i_wb_data;
		wr_sel  <= i_wb_sel;
	end

	reg	[31:0]	txmem	[0:((1<<MAW)-1)];
	reg	[31:0]	rxmem	[0:((1<<MAW)-1)];

	reg	[(MAW+1):0]	tx_len;

	(* ASYNC_REG = "TRUE" *) reg	rx_broadcast;
	(* ASYNC_REG = "TRUE" *) reg	[(MAW+1):0]	rx_len;

	reg	tx_cmd, tx_cancel;
	reg	tx_busy;
	reg	config_hw_crc, config_hw_mac, config_hw_ip_check;
	reg	rx_crcerr, rx_err, rx_miss, rx_clear;
	reg	rx_valid, rx_busy;
	reg	rx_wb_valid, pre_ack, pre_cmd, tx_nzero_cmd;
	reg	[4:0]	caseaddr;
	reg	[31:0]	rx_wb_data, tx_wb_data;
	reg		rx_err_stb, rx_miss_stb, rx_crc_stb;

	reg	[47:0]	hw_mac;
	reg		p_rx_clear;
	reg	[7:0]	clear_pipe;

	reg	[1:0]	tx_spd;

	wire		rx_full_duplex, rx_link_up;
	wire	[1:0]	rx_link_spd;

	initial	config_hw_crc = 0;
	initial	config_hw_mac = 0;
	initial	config_hw_ip_check = 0;
	initial	o_net_reset_n = 1'b0;
	//
	initial	tx_cmd    = 1'b0;
	initial	tx_cancel = 1'b0;
	initial	tx_spd    = 2'b00;
	//
	initial	rx_crcerr = 1'b0;
	initial	rx_err    = 1'b0;
	initial	rx_miss   = 1'b0;
	initial	rx_clear  = 1'b0;
	always @(posedge i_wb_clk)
	begin
		// if (i_wb_addr[(MAW+1):MAW] == 2'b10)
			// Writes to rx memory not allowed here
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr[(MAW+1):MAW] == 2'b11)
				&&(i_wb_sel[3]))
			txmem[i_wb_addr[(MAW-1):0]][31:24] <= i_wb_data[31:24];
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr[(MAW+1):MAW] == 2'b11)
				&&(i_wb_sel[2]))
			txmem[i_wb_addr[(MAW-1):0]][23:16] <= i_wb_data[23:16];
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr[(MAW+1):MAW] == 2'b11)
				&&(i_wb_sel[1]))
			txmem[i_wb_addr[(MAW-1):0]][15:8] <= i_wb_data[15:8];
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr[(MAW+1):MAW] == 2'b11)
				&&(i_wb_sel[0]))
			txmem[i_wb_addr[(MAW-1):0]][7:0] <= i_wb_data[7:0];

		// Set the err bits on these conditions (filled out below)
		if (rx_err_stb)
			rx_err <= 1'b1;
		if (rx_miss_stb)
			rx_miss <= 1'b1;
		if (rx_crc_stb)
			rx_crcerr <= 1'b1;

		if ((wr_ctrl)&&(wr_addr==3'b000))
		begin // RX command register
			if (wr_sel[2])
			begin
				if (wr_data[18])
					rx_crcerr <= rx_crc_stb;
				if (wr_data[17])
					rx_err  <= rx_err_stb;
				if (wr_data[16])
					rx_miss <= rx_miss_stb;
			end
			// busy bit cannot be written to
			if (wr_sel[1])
				rx_clear <= rx_clear || (wr_data[14]);
			// Length bits are cleared when invalid
		end else if (!rx_valid)
			rx_clear <= 1'b0;

		clear_pipe <= { clear_pipe[6:0], rx_clear };
		p_rx_clear <= |clear_pipe;

		if ((tx_busy)||(tx_cancel))
			tx_cmd <= 1'b0;
		if (!tx_busy)
			tx_cancel <= 1'b0;
		pre_cmd <= 1'b0;
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
				pre_cmd <= (wr_data[14]);
				tx_cancel <= (tx_busy)&&(!wr_data[14]);
			end

			if (wr_sel[1:0] == 2'b11)
			begin
//		14'h0	| SW-CRCn |NET-RST|BUSY/CMD | 14 bit length(in octets)|
				if (!tx_cmd && !tx_busy)
					tx_len <= wr_data[(MAW+1):0];
			end
		end 
		tx_nzero_cmd <= ((pre_cmd)&&(tx_len != 0));
		if (tx_nzero_cmd)
			tx_cmd <= 1'b1;
		if (!o_net_reset_n)
			tx_cancel <= 1'b1;
		if (!o_net_reset_n)
			tx_cmd <= 1'b0;

		if ((wr_ctrl)&&(wr_addr==3'b010))
		begin
			if (wr_sel[1])
				hw_mac[47:40] <= wr_data[15:8];
			if (wr_sel[0])
				hw_mac[39:32] <= wr_data[7:0];
		end
		if ((wr_ctrl)&&(wr_addr==3'b011))
		begin
			if (wr_sel[3])
				hw_mac[31:24] <= wr_data[31:24];
			if (wr_sel[2])
				hw_mac[23:16] <= wr_data[23:16];
			if (wr_sel[1])
				hw_mac[15: 8] <= wr_data[15: 8];
			if (wr_sel[0])
				hw_mac[ 7: 0] <= wr_data[ 7: 0];
		end
	end

	wire	[31:0]	w_tx_ctrl;
	wire	[31:0]	w_rx_ctrl;
	wire	[3:0]	w_maw;

	assign	w_maw = MAW+2; // Number of bits in the packet length field
	assign	w_rx_ctrl = {
			rx_link_spd, !rx_full_duplex, !rx_link_up,  // 4 bits
			w_maw,	// 4 bits
			{(24-20){1'b0}}, // 4 bits
			(rx_valid)&&(rx_broadcast)&&(!rx_clear), // 1-bit
			rx_crcerr, rx_err, rx_miss,		// 3-bits
			// 16-bits follow
			rx_busy, (rx_valid)&&(!rx_clear),
			{(14-MAW-2){1'b0}}, rx_len };

	assign	w_tx_ctrl = { tx_spd, 2'b00, w_maw, {(24-20){1'b0}}, 
			((RXSCOPE) ? 1'b0:1'b1),
			!config_hw_ip_check,
			!o_net_reset_n,!config_hw_mac,
			// 16 bits follow
			!config_hw_crc, tx_busy,
				{(14-MAW-2){1'b0}}, tx_len };

	reg	[31:0]	counter_rx_miss, counter_rx_err, counter_rx_crc;
	initial	counter_rx_miss = 32'h00;
	initial	counter_rx_err  = 32'h00;
	initial	counter_rx_crc  = 32'h00;

	// Reads from the bus ... always done, regardless of i_wb_we
	always @(posedge i_wb_clk)
	begin
		rx_wb_data  <= rxmem[i_wb_addr[(MAW-1):0]];
		rx_wb_valid <= (i_wb_addr[(MAW-1):0] <= { rx_len[(MAW+1):2] });
		tx_wb_data  <= txmem[i_wb_addr[(MAW-1):0]];
		pre_ack  <= (i_wb_stb)&&(!i_reset);
		caseaddr <= {i_wb_addr[(MAW+1):MAW], i_wb_addr[2:0] };

		casez(caseaddr)
		5'h00: o_wb_data <= w_rx_ctrl;
		5'h01: o_wb_data <= w_tx_ctrl;
		5'h02: o_wb_data <= {16'h00, hw_mac[47:32] };
		5'h03: o_wb_data <= hw_mac[31:0];
		5'h04: o_wb_data <= counter_rx_miss;
		5'h05: o_wb_data <= counter_rx_err;
		5'h06: o_wb_data <= counter_rx_crc;
		5'h07: o_wb_data <= 32'h00;
		5'b10???: o_wb_data <= (rx_wb_valid)?rx_wb_data:32'h00;
		5'b11???: o_wb_data <= tx_wb_data;
		default: o_wb_data <= 32'h00;
		endcase
		o_wb_ack <= (pre_ack)&&(i_wb_cyc)&&(!i_reset);
	end


	/////////////////////////////////////
	//
	//
	//
	// Reset crosses clock domains
	//
	//
	//
	/////////////////////////////////////
	wire	n_tx_reset, n_rx_reset;
`ifdef	VERILATOR
	assign	n_tx_reset = i_reset;
	assign	n_rx_reset = i_reset;
`else
	reg	[1:0]	q_tx_reset, q_rx_reset;

	always @(posedge i_net_rx_clk or posedge i_reset)
	if(i_reset)
		q_rx_reset <= 2'b11;
	else
		q_rx_reset <= { q_rx_reset[0], 1'b0 };

	assign	n_rx_reset = q_rx_reset[1];

	always @(posedge i_net_tx_clk or posedge i_reset)
	if(i_reset)
		q_tx_reset <= 2'b11;
	else
		q_tx_reset <= { q_tx_reset[0], 1'b0 };

	assign	n_tx_reset = q_tx_reset[1];
`endif


	/////////////////////////////////////
	//
	//
	//
	// Transmitter code
	//
	//
	//
	/////////////////////////////////////
	(* ASYNC_REG = "TRUE" *) reg	[(MAW+1):0]	n_tx_len;
	(* ASYNC_REG = "TRUE" *) reg r_tx_cmd, r_tx_cancel;
	reg		n_tx_cmd, n_tx_cancel, n_still_busy;
	wire	[1:0]	n_tx_spd;
	wire		tx_ce;
	wire		w_memv, w_macen, w_paden, w_txcrcen, w_txprev;
	wire	[7:0]	w_memd, w_macd,  w_padd,  w_txcrcd,  w_txpred;

	initial	{ n_tx_cmd, r_tx_cmd } = 0;
	initial	{ n_tx_cancel, r_tx_cancel } = 0;
	always @(posedge i_net_tx_clk)
	begin
		{ n_tx_cmd,    r_tx_cmd }    <= { r_tx_cmd,    tx_cmd };
		{ n_tx_cancel, r_tx_cancel } <= { r_tx_cancel, tx_cancel };
	end

	tfrvalue #(.NB(2))
	tfrtxspd(i_wb_clk, tx_spd, i_net_tx_clk, n_tx_spd);

	wire	[MAW-1:0]	n_tx_addr;
	reg	[31:0]		n_tx_data;
	reg			n_tx_complete;
	(* ASYNC_REG = "TRUE" *) reg	n_tx_busy,
					n_tx_config_hw_mac, n_tx_config_hw_crc;

	initial	n_tx_busy  = 1'b0;
	initial	n_tx_complete  = 1'b0;
	always @(posedge i_net_tx_clk)
	if (n_tx_reset || n_tx_cancel)
	begin
		n_tx_busy <= 1'b0;
		n_tx_complete <= 1'b0;
	end else if (!n_tx_busy)
	begin
		if (n_tx_cmd)
		begin
			n_tx_busy     <= 1'b1;
			n_tx_complete <= 1'b0;
		end
	end else if (tx_ce && o_net_tx_ctl && !w_txprev)
	begin
		n_tx_busy     <= 1'b0;
		n_tx_complete <= 1'b1;
	end

	always @(posedge i_net_tx_clk)
	if (!n_tx_busy)
	begin
		n_tx_config_hw_mac <= config_hw_mac;
		n_tx_config_hw_crc <= config_hw_crc;
		n_tx_len <= tx_len;
	end

	//
	// Control the read address to the transmit memory when reading in order to transmit
	//
	txeaddr #(.LGNBYTES(MAW+2))
	txeaddri(i_net_tx_clk, n_tx_reset || n_tx_cancel, tx_ce,
		n_tx_cmd, n_tx_len, n_tx_addr, n_tx_data, w_memv, w_memd);

	// Read from the transmit memory
	always @(posedge i_net_tx_clk)
		n_tx_data  <= txmem[n_tx_addr];

	wire	n_tx_config_hw_preamble;
	assign	n_tx_config_hw_preamble = 1'b1;

`ifndef	TX_BYPASS_HW_MAC
	addemac	txmaci(i_net_tx_clk, ((n_tx_reset)||(n_tx_cancel)), tx_ce,
				n_tx_config_hw_mac, hw_mac,
				w_memv, w_memd, w_macen, w_macd);
`else
	assign	w_macen = w_memv;
	assign	w_macd  = w_memd;
`endif

`ifndef	TX_BYPASS_PADDING
	addepad	txpadi(i_net_tx_clk, ((n_tx_reset)||(n_tx_cancel)), tx_ce,
				w_macen, w_macd, w_paden, w_padd);
`else
	assign	w_paden = w_macen;
	assign	w_padd  = w_macd;
`endif

`ifndef	TX_BYPASS_HW_CRC
	addecrc	txcrci(i_net_tx_clk, ((n_tx_reset)||(n_tx_cancel)), tx_ce,
				n_tx_config_hw_crc,
				w_paden, w_padd, w_txcrcen, w_txcrcd);
`else
	assign	w_txcrcen = w_macen;
	assign	w_txcrcd  = w_macd;
`endif

	// wire	w_net_tx_ctl;
	addepreamble txprei(i_net_tx_clk, ((n_tx_reset)||(n_tx_cancel)), tx_ce,
				n_tx_config_hw_preamble,
				w_txcrcen, w_txcrcd, w_txprev, w_txpred);

	//
	// txespeed helps us support 10Mbps, 100Mbps, and 1Gbps
	// without changing clock speed
	//
	txespeed txspdi(i_net_tx_clk, n_tx_reset, n_tx_spd,
			w_txprev, w_txpred,
			o_net_tx_ctl, o_net_txd, tx_ce, o_net_tx_ck);

	initial	n_still_busy = 0;
	always @(posedge i_net_tx_clk)
		n_still_busy <= (n_tx_busy || o_net_tx_ctl || w_txcrcen || w_macen || w_paden);

	(* ASYNC_REG = "TRUE" *) reg	r_tx_busy;
	always @(posedge i_wb_clk)
	begin
		{ tx_busy, r_tx_busy } <= { r_tx_busy, n_still_busy };
	end





	/////////////////////////////////////
	//
	//
	//
	// Receiver code
	//
	//
	//
	/////////////////////////////////////

	(* ASYNC_REG = "TRUE" *) reg n_rx_config_hw_mac, n_rx_config_hw_crc,
			n_rx_config_ip_check;
	(* ASYNC_REG = "TRUE" *) reg r_rx_clear;
	wire	rx_ce;

	assign	rx_ce = 1'b1;

	reg	n_rx_clear;
	always @(posedge i_net_rx_clk)
	begin
		r_rx_clear <= (p_rx_clear)||(!o_net_reset_n);
		n_rx_clear <= r_rx_clear;
	end


	reg		n_rx_net_err;
	wire		w_npre,  w_rxmin,  w_rxcrc,  w_rxmac;
	wire	[7:0]	w_npred, w_rxmind, w_rxcrcd, w_rxmacd;
	wire		w_minerr, w_rxcrcerr, w_macerr, w_broadcast, w_iperr;

`ifndef	RX_BYPASS_HW_PREAMBLE
	rxepreambl rxprei(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)), 1'b1, 1'b1,
			i_net_rx_dv, i_net_rxd, w_npre, w_npred);
`else
	assign	w_npre  = i_net_rx_ctl; 
	assign	w_npred = 1'b0; 
`endif

`ifdef	RX_BYPASS_HW_MINLENGTH
	// Insist on a minimum of 64-byte packets
	rxemin	rxmini(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)), 1'b1,
			w_npre, w_minerr);
`else
	assign	w_minerr= 1'b0;
`endif
	assign	w_rxmin = w_npre;
	assign	w_rxmind= w_npred;

`ifndef	RX_BYPASS_HW_CRC
	rxecrc	rxcrci(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)), rx_ce,
			n_rx_config_hw_crc,
			w_rxmin, w_rxmind, w_rxcrc, w_rxcrcd, w_rxcrcerr);
`else
	assign	w_rxcrc   = w_rxmin;
	assign	w_rxcrcd  = w_rxmind;
	assign	w_rxcrcerr= 1'b0;
`endif

`ifndef	RX_BYPASS_HW_RMMAC
	rxehwmac rxmaci(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)),
			rx_ce, n_rx_config_hw_mac, hw_mac,
			w_rxcrc, w_rxcrcd,
			w_rxmac, w_rxmacd,
			w_macerr, w_broadcast);
`else
	assign	w_rxmac  = w_rxcrc;
	assign	w_rxmacd = w_rxcrcd;
`endif

`define	RX_HW_IPCHECK
`ifdef	RX_HW_IPCHECK
	// Check: if this packet is an IP packet, is the IP header checksum
	// valid?
	rxeipchk rxipci(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)),
			rx_ce, n_rx_config_ip_check,
			w_rxcrc, w_rxcrcd, w_iperr);
`else
	assign	w_iperr = 1'b0;
`endif

	wire			w_rxwr;
	wire	[(MAW-1):0]	w_rxaddr;
	wire	[31:0]		w_rxdata;
	wire	[(MAW+1):0]	w_rxlen;

	rxewrite #(MAW) rxememi(i_net_rx_clk, ((n_rx_reset)||(n_rx_net_err)),
			rx_ce, w_rxmac, w_rxmacd,
			w_rxwr, w_rxaddr, w_rxdata, w_rxlen);

	reg	last_rxwr, n_rx_valid, n_eop, n_rx_busy, n_rx_crcerr,
		n_rx_err, n_rx_broadcast, n_rx_miss;
	reg	[(MAW+1):0]	n_rx_len;
	reg		n_rx_full_duplex, n_rx_link_up;
	reg	[1:0]	n_rx_link_spd;

	always @(*)
		n_eop = (!w_rxwr)&&(last_rxwr)&&(!n_rx_net_err);

	initial	n_rx_valid = 1'b0;
	initial	n_rx_clear = 1'b1;
	initial	n_rx_miss  = 1'b0;
	always @(posedge i_net_rx_clk)
	begin
		if ((w_rxwr)&&(!n_rx_valid))
			rxmem[w_rxaddr] <= w_rxdata;

		// n_rx_net_err goes true as soon as an error is detected,
		// and stays true as long as valid data is coming in
		n_rx_net_err <= (i_net_rx_dv)&&(
				i_net_rx_err	// PHY sensed a collision
				||(w_minerr)||(w_macerr)||(w_rxcrcerr)
				||(w_iperr)
				||(n_rx_net_err)
				||((w_rxwr)&&(n_rx_valid)));

		last_rxwr <= w_rxwr;

		n_rx_busy <= (!n_rx_net_err)&&((i_net_rx_dv)||(w_npre)||(w_rxmin)
			||(w_rxcrc)||(w_rxmac)||(w_rxwr));

		// Oops ... we missed a packet
		n_rx_miss <= (n_rx_valid)&&(w_rxwr)||
			((n_rx_miss)&&(!n_rx_clear));

		n_rx_crcerr <= ((w_rxcrcerr)&&(!n_rx_net_err))
			||((n_rx_crcerr)&&(!n_rx_clear));

		n_rx_err <= ((n_rx_err)&&(!n_rx_clear))||(w_minerr);

		n_rx_broadcast <= (w_broadcast)||((n_rx_broadcast)&&(!n_rx_clear));

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

		if (n_rx_clear)
		begin
			n_rx_valid <= 1'b0;
			n_rx_len <= 0;
		end else if (n_eop)
		begin
			n_rx_valid <= 1'b1;
			n_rx_len   <= w_rxlen - ((n_rx_config_hw_crc)?{{(MAW-1){1'b0}},3'h5}:0);
		end
		// else n_rx_valid = n_rx_valid;

		if ((!i_net_rx_dv)||(n_rx_clear))
		begin
			n_rx_config_hw_mac   <= config_hw_mac;
			n_rx_config_hw_crc   <= config_hw_crc;
			n_rx_config_ip_check <= config_hw_ip_check;
		end
	end

	tfrvalue #(.NB(4))
	tfrrxspd(i_net_rx_clk,
		{ n_rx_full_duplex, n_rx_link_spd, n_rx_link_up },
		i_wb_clk,
		{ rx_full_duplex, rx_link_spd, rx_link_up });

	reg	r_rx_busy, r_rx_valid;
	always @(posedge i_wb_clk)
	begin
		r_rx_valid <= n_rx_valid;
		rx_valid <= r_rx_valid;

		r_rx_busy <= n_rx_busy;
		rx_busy <= r_rx_busy;

		rx_len <= n_rx_len;
		rx_broadcast <= n_rx_broadcast;
	end

	reg	[3:0]	rx_err_pipe, rx_miss_pipe, rx_crc_pipe;

	always @(posedge i_wb_clk)
	begin
		rx_err_pipe  <= { rx_err_pipe[ 2:0],(n_rx_err)  };
		rx_miss_pipe <= { rx_miss_pipe[2:0],(n_rx_miss) };
		rx_crc_pipe  <= { rx_crc_pipe[ 2:0],(n_rx_crcerr) };
		rx_err_stb   <= (rx_err_pipe[ 3:2] == 2'b01);
		rx_miss_stb  <= (rx_miss_pipe[3:2] == 2'b01);
		rx_crc_stb   <= (rx_crc_pipe[ 3:2] == 2'b01);
	end


	always @(posedge i_wb_clk)
	if (o_net_reset_n)
		counter_rx_miss <= 32'h0;
	else if (rx_miss_stb)
		counter_rx_miss <= counter_rx_miss + 32'h1;

	always @(posedge i_wb_clk)
	if (o_net_reset_n)
		counter_rx_err <= 32'h0;
	else if (rx_err_stb)
		counter_rx_err <= counter_rx_err + 32'h1;

	always @(posedge i_wb_clk)
	if (o_net_reset_n)
		counter_rx_crc <= 32'h0;
	else if (rx_crc_stb)
		counter_rx_crc <= counter_rx_crc + 32'h1;

	assign	o_tx_int = !tx_busy;
	assign	o_rx_int = (rx_valid)&&(!rx_clear);
	assign	o_wb_stall = 1'b0;

	generate if (RXSCOPE)
	begin : RXSCOPE_DEF

		assign	o_debug_clk = i_net_rx_clk;

		reg	rx_trigger, rx_last_dv;
		reg	rx_dvalid;

		// always @(*)	rx_dvalid = i_net_rx_dv;

		reg	rx_tx_busy;
		always @(posedge i_net_rx_clk)
			{ rx_dvalid, rx_tx_busy }<={ rx_tx_busy, n_still_busy };

		initial	rx_last_dv = 0;
		always @(posedge i_net_rx_clk)
			rx_last_dv <= rx_dvalid;

		initial	rx_trigger = 0;
		always @(posedge i_net_rx_clk)
			rx_trigger <= (rx_dvalid)&&(!rx_last_dv);

		assign	o_debug = {
			// Signals, and Potential errors
			rx_trigger, n_eop, w_macerr, w_broadcast,
			n_rx_clear, n_rx_miss, n_rx_net_err, n_rx_valid,
			n_rx_busy, // 9-bits
			// Memory stage, 1-bits
			w_rxwr,
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


	end else begin : TXSCOPE_DEF

		assign	o_debug_clk = i_net_tx_clk;

		assign	o_debug = {
			// 3 bits
			n_tx_cmd, n_tx_complete, n_tx_busy,
			// 9 bits
			w_memv, w_memd,
			// 2 bits
			w_macen, w_paden,
			// 9-bits
			w_txcrcen, w_txcrcd,
			// 9 bits
			o_net_tx_ctl, o_net_txd
		};
	end endgenerate

endmodule
