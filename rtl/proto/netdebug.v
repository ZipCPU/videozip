////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/netdebug.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	The goal of this module is to convert an IP/UDP port into a
//		debugging bus.  Requests can then be made on this port to read
//	from or write to the bus.
//
//	There will never be a time when two packets are being processed at the
//	same time.  Packets may be buffered on input and/or output, but never
//	both processed at the same time.
//
//	Since the transport is UDP, there is no guarantee of packet delivery,
//	neither is there any guarantee that there won't be repeat packets.
//	Indeed, there will likely be repeats if a return packet is every
//	dropped, when the source transmits the request a second time.
//
//	To mitigate the packet loss problem (with a minimum of logic), all
//	packets (requests) will be given replies.  Further, all replies will
//	reflect a host packet ID given them, and will include a locally
//	generated incrementing packet ID #.
//
//	However, we do have one guarantee: if we receive a packet, it was a
//	valid packet.  It might be a duplicate, it might be out of order, there
//	might've been one missing, but any packet received will be received in
//	whole (not in part) and will be received with CRC and checksums.  It
//	will only be processed if the CRCs (not necessarily checksums) match.
//
//		*NOTE*: Other parts of the network stack are (currently) only
//		checking the Ethernet CRC and the IP Header checksum, not the
//		UDP payload checksum.  I'm assuming this check to be sufficient.
//
// Packet format:
// {{{
//	Incoming Packet header format (Following UDP header removal):
//		16'b host frame ID #.  This only has meaning if the ID is zero,
//		  in which case it represents the beginning of a transaction
//		  stream from a (potentially) new host.
//
//		8'b GPIO mask.  Any bit set in this mask will cause a bit in the
//		  corresponding GPIO vector to be adjusted using the GPIO values
//		  that come in the next word.
//
//		8'b GPIO values.  These are the values that will be used when
//		  adjusting those bits for which GPIO mask is set.  In other
//		  words ...
//
//			new_gpio = (old_gpio & ~pkt_mask)|(pkt_gpio & pkt_mask);
//
//		The rest of the incoming packet will be processed as a payload
//		to the underlying debugging bus implementation.
//
//	Return packet header format (Before UDP header insertion):
//		16'b host frame ID #.  This is the host frame # of the packet
//		  for which this one is a response.
//		8'b GPIO inputs.  Provides values for up to 8 GPIO inputs,
//		  as feedback for the caller.
//		8'b GPIO outputs. These are the values currently set for the
//		  GPIO outputs.
//		16'b prior host frame ID #.  This is the frame number of the
//		  packet received from this host prior to the current one,
//		  to help mitigate packet resends.
//		16'b Packet counter.  A simple counter, which should help to
//		  determine how many repeats are getting generated.
// }}}
//
// Options:
// {{{
//	The following option(s) are possibilities which may be built into
//	this module at a later time.  For now, they are listed here as part of
//	my notes.
//
//	OPTION: IDLE PACKETS
//		As an option (to be built later), the module will produce idle
//		packets just to say its there.  For now, if a packet with an
//		empty payload shows up, then it will be reflected as an idle
//		packet.
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
`default_nettype none
// }}}
module	netdebug #(
		// {{{
		// parameter [0:0]	OPT_IDLEPKT = 1'b0
		// parameter [0:0]	OPT_SUPPRESS_REPEATS = 1'b0
		parameter [15:0]	DBG_UDPPORT = 6511,
		parameter [7:0]		DEF_GPIO = 8'h0,
		parameter		AW = 30,
		parameter		LGWATCHDOG    = 20,
		localparam		DW = 32
		// }}}
	) (
		// {{{
		input	wire	i_clk, i_reset,
		//
		input	wire	[7:0]	i_gpio,
		output	wire	[7:0]	o_gpio,
		input	wire	[31:0]	i_my_ipaddr,
		//
		// Wishbone bus master
		// {{{
		output	wire			o_wb_cyc, o_wb_stb, o_wb_we,
		output	wire	[AW-1:0]	o_wb_addr,
		output	wire	[DW-1:0]	o_wb_data,
		// output	wire	[DW/8-1:0]	o_wb_sel,
		input	wire			i_wb_stall,
		input	wire			i_wb_ack,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire			i_wb_err,
		// }}}
		// Incoming packet-stream interface
		// {{{
		// We can't operate on an abortable network stream for two
		// reasons:
		//	1. The bus is running at a slower speed, so therefore
		//		TDATA's width must be wider
		//	2. (Was that my two reasons?)
		//	3. We want to treat each packet as atomic: it will
		//		be guaranteed complete.
		input	wire			S_AXI_TVALID,
		output	wire			S_AXI_TREADY,
		input	wire	[DW-1:0]	S_AXI_TDATA,
		// }}}
		// Outgoing packet-stream interface
		//  {{{
		output	wire			M_AXI_TVALID,
		input	wire			M_AXI_TREADY,
		output	wire	[DW-1:0]	M_AXI_TDATA,
		// }}}
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	// localparam	LGINPUT_FIFO  = 4;
	localparam	LGOUTPUT_FIFO = 4;

	// Incoming packet payload processing
	wire		pl_valid, pl_busy, pl_ready, pl_last;
	wire	[7:0]	pl_data;

	wire		soft_reset, ignored_reset;
	reg		r_wdt_reset;


	// Incoming code word, once processed
	wire		in_stb;
	wire	[35:0]	in_word;

	// Input FIFO
	wire		ififo_rd;
	wire	[35:0]	ififo_codword;
	wire		ififo_empty_n, ififo_full;


	// Code word outputs from running the bus
	wire		exec_stb;
	wire	[35:0]	exec_word;

	// Output FIFO
	wire		ofifo_rd;
	wire	[35:0]	ofifo_codword;
	wire		ofifo_err, ofifo_empty_n;

	wire		w_bus_busy, w_bus_reset;
	reg	[(LGWATCHDOG-1):0]	r_wdt_timer;
	reg		handler_busy;

	wire		out_stb;
	reg		out_last;
	wire	[7:0]	out_byte;
	wire		output_busy;
	wire		in_active;
	wire		out_active;

	wire		w_sync, w_repeat_stb;
	wire	[47:0]	host_mac;
	wire	[31:0]	host_ip;
	wire	[15:0]	host_sport;
	wire	[15:0]	host_frameid;

	wire		pkt_pvalid, pkt_pready, pkt_plast, pkt_busy,
			pkt_ready, pkt_active, pkt_pabort;
	wire	[31:0]	pkt_pdata;

	wire		udp_hdr_valid, udp_hdr_ready, udp_hdr_last;
	wire	[31:0]	udp_hdr_data;

	wire		M_AXI_TLAST;
	wire		dbgtx_overflow;
	reg		interrupt_flag, int_ackd, err_flag, overflow_flag;
	reg	[15:0]	return_gpio;

	reg	r_soft_reset;

	// Verilator lint_off UNUSED
	wire	[31:0]	main_debug, dbgrx_debug, dbgtx_debug, udp_debug;
	// Verilator lint_on  UNUSED
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (External) Incoming packet handler
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// handler_busy
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		handler_busy <= 0;
	else if (pl_valid || exec_stb || w_sync || w_repeat_stb || out_active)
		handler_busy <= 1;
	else if (pkt_pvalid && (!pkt_plast || !pkt_pready))
		handler_busy <= 1;
	else if (pkt_pvalid)
		handler_busy <= 0;
	// }}}

	// out_last
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		out_last <= 0;
	else if (pl_valid || in_active || w_bus_busy || in_stb || exec_stb)
		out_last <= 0;
	else
		out_last <= 1;
	// }}}

	netdbgrx #(
		.GPIO_AUTO_CLEAR(8'h0f),
		.DEF_GPIO(DEF_GPIO)
	) u_dbgrx (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Incoming packet
		// {{{
		.S_AXI_TVALID(S_AXI_TVALID),
		.S_AXI_TREADY(S_AXI_TREADY),
		.S_AXI_TDATA(S_AXI_TDATA),
		// }}}
		.o_gpio(o_gpio),
		.o_sync(w_sync), .o_repeat_stb(w_repeat_stb),
		.o_host_mac(host_mac), .o_host_ip(host_ip),
		.o_host_udpport(host_sport), .o_host_frameid(host_frameid),
		.i_handler_busy(handler_busy),
		// Payload interface
		// {{{
		.M_AXI_TVALID(pl_valid), .M_AXI_TREADY(pl_ready || !pl_data[7]),
		.M_AXI_TDATA(pl_data), .M_AXI_TLAST(pl_last),
		// }}}
		.o_debug(dbgrx_debug)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Decode ASCII input requests into WB bus cycle requests
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbuinput
	getinput(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_stb(pl_valid && pl_data[7]), .o_busy(pl_busy),
			.i_byte({ 1'b0, pl_data[6:0] }),
		.o_soft_reset(ignored_reset),
		.o_stb(in_stb), .o_codword(in_word), .i_busy(ififo_full),
			.o_active(in_active)
		// }}}
	);

	assign	pl_ready = !pl_busy;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Input FIFO (IS THIS REALLY NEEDED, NOW THAT WE HAVE BACKPRESSURE?)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Given that we can support proper back pressure, there's really no
	// reason to have a FIFO any more.  We'll just completely bypass it
	// here instead.
	//

	assign	ififo_empty_n = in_stb;
	assign	ififo_codword = in_word;

	assign	ififo_rd      = ififo_empty_n;
	assign	ififo_full    = w_bus_busy;

	assign	w_bus_reset = r_wdt_reset;
	/*
	assign	ififo_rd = (!w_bus_busy)&&(ififo_empty_n);

	sfifo	#(
		// {{{
		.BW(36),.LGFLEN(LGINPUT_FIFO)
		// }}}
	) padififo(
		// {{{
		.i_clk(i_clk), .i_reset(w_bus_reset),
		.i_wr(in_stb), .i_data(in_word),
			.o_full(ififo_full), .o_fill(ififo_fill),
		.i_rd(ififo_rd), .o_data(ififo_codword),
			.o_empty(ififo_empty)
		// }}}
	);

	assign	ififo_empty_n = !ififo_empty;
	*/

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Run the bus
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Take requests in, Run the bus, send results out
	// This only works if no requests come in while requests
	// are pending.
	wbuexec #(
		.OPT_COUNT_FIFO(1'b1),
		.LGFIFO(LGOUTPUT_FIFO),
		.AW(AW)
	) runwb (
		// {{{
		.i_clk(i_clk), .i_reset(r_wdt_reset || soft_reset),
		.i_valid(ififo_rd), .i_codword(ififo_codword),
			.o_busy(w_bus_busy),
		.o_wb_cyc(o_wb_cyc), .o_wb_stb(o_wb_stb), .o_wb_we(o_wb_we),
			.o_wb_addr(o_wb_addr), .o_wb_data(o_wb_data),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
			.i_wb_data(i_wb_data), .i_wb_err(i_wb_err),
		.o_stb(exec_stb), .o_codword(exec_word), .i_fifo_rd(ofifo_rd)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	ofifo_rd = ofifo_empty_n && !output_busy;
	wbufifo #(
		.BW(36), .LGFLEN(LGOUTPUT_FIFO)
	) busoutfifo (
		// {{{
		.i_clk(i_clk), .i_reset(r_wdt_reset || soft_reset),
		.i_wr(exec_stb), .i_data(exec_word),
		.i_rd(ofifo_rd), .o_data(ofifo_codword),
			.o_empty_n(ofifo_empty_n),
			.o_err(ofifo_err)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Encode bus outputs into a serial data stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wbuoutput #(
		.OPT_COMPRESSION(1'b1),
		.OPT_IDLES(1'b0)
	) wroutput(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || soft_reset),
			.i_soft_reset(w_sync || w_bus_reset || soft_reset),
		.i_stb(ofifo_rd), .i_codword(ofifo_codword),
			.o_busy(output_busy),
		.i_wb_cyc(o_wb_cyc), .i_int(1'b0),
			.i_bus_busy(exec_stb || ofifo_empty_n),
		.o_stb(out_stb), .o_char(out_byte), .i_tx_busy(pkt_busy),
			.o_active(out_active)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog timer
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Add in a watchdog timer to the bus
	initial	r_wdt_reset = 1'b0;
	initial	r_wdt_timer = 0;
	always @(posedge i_clk)
	if (i_reset || soft_reset)
	begin
		r_wdt_timer <= 0;
		r_wdt_reset <= 1'b1;
	end else if (!o_wb_cyc || i_wb_ack)
	begin
		// We're inactive, or the bus has responded: reset the timer
		// {{{
		r_wdt_timer <= 0;
		r_wdt_reset <= 1'b0;
		// }}}
	end else if (&r_wdt_timer)
	begin	// TIMEOUT!!!
		// {{{
		r_wdt_reset <= 1'b1;
		r_wdt_timer <= 0;
		// }}}
	end else begin // Tick-tock ...
		// {{{
		r_wdt_timer <= r_wdt_timer+{{(LGWATCHDOG-1){1'b0}},1'b1};
		r_wdt_reset <= 1'b0;
		// }}}
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Flag generation and handling
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_reset)
		r_soft_reset <= 1'b0;
	else if (pkt_pvalid && !pkt_pready && o_gpio[1])
		r_soft_reset <= 1'b1;
	else if (!pkt_pvalid || pkt_pready)
		r_soft_reset <= 1'b0;

	assign	soft_reset = o_gpio[1] || r_soft_reset;

	always @(posedge i_clk)
	if (i_reset)
		int_ackd <= 1'b0;
	else if (i_gpio[0] && interrupt_flag)
		int_ackd <= 1'b1;
	else if (!i_gpio[0])
		int_ackd <= 1'b0;

	always @(posedge i_clk)
	if (i_reset)
		interrupt_flag <= 1'b0;
	else if (i_gpio[0])
		interrupt_flag <= 1'b1;
	else if (!i_gpio[0] && int_ackd)
		interrupt_flag <= 1'b0;

	always @(posedge i_clk)
	if (i_reset)
		err_flag <= 1'b0;
	else if (o_wb_cyc && i_wb_err)
		err_flag <= 1'b1;
	else if (o_gpio[2])
		err_flag <= 1'b0;

	always @(posedge i_clk)
	if (i_reset)
		overflow_flag <= 1'b0;
	else if (dbgtx_overflow)
		overflow_flag <= 1'b1;
	else if (o_gpio[3])
		overflow_flag <= 1'b0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (External) Assemble back into a packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	pkt_busy = !pkt_ready;

	always @(*)
	begin
		return_gpio = { i_gpio, o_gpio };
		if (interrupt_flag)
			return_gpio[8] = 1'b1;
		if (err_flag)
			return_gpio[10] = 1'b1;
		if (overflow_flag)
			return_gpio[11] = 1'b1;
	end

	netdbgtx
	u_dbgtx (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.i_sync(w_sync), .i_gpio(return_gpio),
		.i_repeat_stb(w_repeat_stb), .i_hostid(host_frameid),
		.o_busy(pkt_active),
		.S_AXI_TVALID(out_stb), .S_AXI_TREADY(pkt_ready),
		.S_AXI_TDATA(out_byte), .S_AXI_TLAST(out_last && !out_active),
		.M_AXIN_VALID(pkt_pvalid), .M_AXIN_READY(pkt_pready),
		.M_AXIN_DATA(pkt_pdata), .M_AXIN_LAST(pkt_plast),
		.M_AXIN_ABORT(pkt_pabort),
		.o_overflow(dbgtx_overflow),

		.o_debug(dbgtx_debug)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Turn that packet into UDP
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	ipheader
	u_ipheader (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.i_enet_dest(host_mac), .i_ip_src(i_my_ipaddr),
				.i_ip_dest(host_ip),
		//
		.M_AXI_TVALID(udp_hdr_valid), .M_AXI_TREADY(udp_hdr_ready),
		.M_AXI_TDATA( udp_hdr_data),  .M_AXI_TLAST( udp_hdr_last)
		//
		// }}}
	);

	pkt2udp #(
		.LGMEM(10)
	) u_pkt2udp (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(pkt_pvalid), .S_AXIN_READY(pkt_pready),
		.S_AXIN_DATA( pkt_pdata),  .S_AXIN_LAST( pkt_plast),
		.S_AXIN_ABORT(soft_reset),
		//
		.S_HDR_VALID(udp_hdr_valid), .S_HDR_READY(udp_hdr_ready),
		.S_HDR_DATA( udp_hdr_data),  .S_HDR_LAST( udp_hdr_last),
		//
		.i_udp_sport(DBG_UDPPORT), .i_udp_dport(host_sport),
		//
		.M_AXIS_VALID(M_AXI_TVALID), .M_AXIS_READY(M_AXI_TREADY),
		.M_AXIS_DATA( M_AXI_TDATA),  .M_AXIS_LAST( M_AXI_TLAST),
		//
		.o_debug(udp_debug)
		// }}}
	);

	/*
	assign	udp_debug = {
			M_AXI_TVALID, 8'h0,
			(host_ip == 32'h010fa8c0) ? 1'b1:1'b0,
			(host_ip == 32'hc0a80f01) ? 1'b1:1'b0,
			(host_ip != 32'h00) ? 1'b1:1'b0,
			(host_sport != 16'h00) ? 1'b1:1'b0,
			pkt_pvalid, pkt_pready, pkt_plast,
				soft_reset, // pkt_pdata
			udp_hdr_valid, udp_hdr_ready, udp_hdr_last,
			M_AXI_TVALID, M_AXI_TREADY, M_AXI_TLAST,
			M_AXI_TDATA[8:0]
		};
	*/
	// }}}

	assign	main_debug = {
			w_sync || w_bus_reset || in_stb,

			S_AXI_TVALID, // S_AXI_TREADY,

			w_sync, in_stb, out_last, out_active, // exec_stb
			pl_valid, pl_ready, pl_last, pl_data[6:0],

			M_AXI_TVALID, M_AXI_TREADY,			// 16
			M_AXI_TLAST, pkt_pvalid, pkt_pready, pkt_plast, //
			out_stb, pkt_ready, out_byte
			};

	// assign	o_debug = dbgrx_debug;
	// assign	o_debug = dbgtx_debug;
	// assign	o_debug = main_debug;
	assign	o_debug = udp_debug;

	// Keep Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ofifo_err, i_gpio, pl_last, pkt_pabort,
			M_AXI_TLAST, pkt_active, ignored_reset };
	// verilator lint_on  UNUSED
	// }}}
endmodule
