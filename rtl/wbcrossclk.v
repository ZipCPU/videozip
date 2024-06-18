////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/wbcrossclk.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To cross clock domains with a (pipelined) wishbone bus.
//
//	Challenges:
//	1. Wishbone has no capacity for back pressure.  That means that we'll
//		need to be careful not to issue more STB requests than ACKs
//		that will fit in the return buffer.
//
//	    Imagine, for example, a faster return clock but a slave that needs
//		many clocks to get going.  During that time, many requests
//		might be issued.  If they all suddenly get returned at once,
//		flooding the return ACK FIFO, then we have a problem.
//
//	2. Bus aborts.  If we ever have to abort a transaction, that's going
//		to be a pain.  The FIFOs will need to be reset and the
//		downstream CYC line dropped.  This needs to be done
//		synchronously in both domains, but there's no real choice but
//		to make the crossing asynchronous.
//
//	3. Synchronous CYC.  Lowering CYC is a normal part of the protocol, as
//		is raising CYC.  CYC is used as a bus locking scheme, so we'll
//		need to know when it is (properly) lowered downstream.  This
//		can be done by passing a synchronous CYC drop request through
//		the pipeline in addition to the bus aborts above.
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
module	wbcrossclk(i_wb_clk,
		// The input bus
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel,
			o_wb_stall, o_wb_ack, o_wb_data, o_wb_err,
		// The delayed bus
		i_xclk_clk,
		o_xclk_cyc, o_xclk_stb, o_xclk_we, o_xclk_addr,o_xclk_data,o_xclk_sel,
			i_xclk_ack, i_xclk_stall, i_xclk_data, i_xclk_err);
	parameter	AW=32, DW=32, DELAY_STALL = 0, LGFIFO = 5;
	parameter [(LGFIFO-1):0]	THRESHOLD = {{(LGFIFO-4){1'b0}},4'h8};

	input	wire			i_wb_clk;
	// Input/master bus
	input	wire			i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[(AW-1):0]	i_wb_addr;
	input	wire	[(DW-1):0]	i_wb_data;
	input	wire	[(DW/8-1):0]	i_wb_sel;
	output	reg			o_wb_ack;
	output	reg			o_wb_stall;
	output	reg	[(DW-1):0]	o_wb_data;
	output	reg			o_wb_err;
	// Delayed bus
	input	wire			i_xclk_clk;
	output	wire			o_xclk_cyc;
	output	reg			o_xclk_stb;
	output	wire			o_xclk_we;
	output	wire	[(AW-1):0]	o_xclk_addr;
	output	wire	[(DW-1):0]	o_xclk_data;
	output	wire	[(DW/8-1):0]	o_xclk_sel;
	input	wire			i_xclk_ack;
	input	wire			i_xclk_stall;
	input	wire	[(DW-1):0]	i_xclk_data;
	input	wire			i_xclk_err;

	localparam	TFRCLOCKS = 2;
	localparam	IFIFOWD   = 1+AW+DW+DW/8;
	localparam	OFIFOWD   = 1+DW;
	localparam	FIFOLN    = (1<<LGFIFO);

	reg	[(TFRCLOCKS-1):0]	tfr_cyc;
	reg	[(IFIFOWD-1):0]		req_fifo	[(FIFOLN-1):0];
	reg	[(OFIFOWD-1):0]		ack_fifo	[(FIFOLN-1):0];
	reg	[(IFIFOWD-1):0]		xclk_fifo_data;
	reg	[(LGFIFO-1):0]		req_head, xclk_tail, ack_head,
					wb_ack_tail;
	wire	[(LGFIFO-1):0]		xclk_req_head, wb_ack_head;

	//
	//
	// On the original wishbone clock ...
	//
	//	 FIFO/queue up our requests
	//
	reg	our_cyc, bus_abort;

	initial	our_cyc = 1'b0;
	always	@(posedge i_wb_clk)
	if (i_reset || !i_wb_cyc)
		our_cyc <= 1'b0;
	else if (!i_wb_cyc || o_wb_ack)
		our_cyc <= 1'b0;
	else if (i_wb_stb)
		our_cyc <= 1'b1;

	initial	{ bus_abort, bus_abort_pipe } = -1;
	always	@(posedge i_wb_clk)
	if (i_reset)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (!i_wb_cyc && !ack_fifo_empty)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (o_wb_err && !ack_fifo_single)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (ack_fifo_empty)
		{ bus_abort, bus_abort_pipe } <= { bus_abort_pipe, 1'b0 };

	//
	// Cross clock domain
	//
	initial	{ xck_reset, xck_reset_pipe } = -1;
	always	@(posedge i_xck or posedge bus_abort)
	if (bus_abort)
		{ xck_reset, xck_reset_pipe } <= 3'b111;
	else
		{ xck_reset, xck_reset_pipe } <= { xck_reset_pipe, 1'b0 };


	//
	// Issuing requests
	//
	afifo #(.WIDTH(2+AW+DW+(DW/8)))
	reqfifo(.i_wclk(i_wb_clk), .i_wr_reset_n(!bus_abort),
		.i_wr(i_wb_stb || (last_wb_active && !i_wb_cyc)),
		.i_wdata({ i_wb_stb, i_wb_we, i_wb_addr, i_wb_data, i_wb_sel }),
		.o_wr_full(req_fifo_stall),
		//
		.i_rclk(i_xck), .i_rd_reset_n(!xck_reset),
		.i_rd(o_xclk_cyc && (!o_xclk_stb || i_xclk_stall)),
		.i_rdata({ req_stb, o_xclk_we, o_xclk_addr, o_xclk_data, o_xclk_sel }),
		.o_rd_empty(req_fifo_empty));

	always @(posedge i_xck)
	if (xck_reset)
		xclk_err_state <= 1'b0;
	else if (o_xclk_cyc && i_xclk_err)
		xclk_err_state <= 1'b1;

	always @(posedge i_xck)
	if (xck_reset || (o_xclk_cyc && i_xclk_err))
		o_xclk_cyc = 1'b0;
	else if (!req_fifo_empty)
		o_xclk_cyc = req_stb;

	always @(*)
		o_xclk_stb = req_stb && o_xclk_cyc && !req_fifo_empty;

	//
	// Request counting
	//
	always @(posedge i_wb_clk)
	if (i_reset || !i_wb_cyc || o_wb_err)
		acks_outstanding <= 0;
	else case({ (i_wb_stb && !o_wb_stall), o_wb_ack })
	2'b10: acks_outstanding <= acks_outstanding + 1;
	2'b01: acks_outstanding <= acks_outstanding - 1;
	default: begin end
	endcase

	always @(*)
		ack_fifo_single = (acks_outstanding == 1);

	always @(*)
		ack_fifo_empty = (acks_outstanding == 0);

	assign	o_wb_stall = ack_fifo_full || bus_abort;

	//
	// The return pipeline
	//
	afifo #(.WIDTH(2+AW+DW+(DW/8)))
	ackfifo(.i_wclk(i_xck), .i_wr_reset_n(!bus_abort),
		.i_wr({ i_xclk_ack || i_xclk_err })
		.i_wdata({ i_xclk_ack, i_xclk_err, i_xclk_data })
		.o_wr_full(ign_ack_fifo_stall),
		//
		.i_rclk(i_wb_clk), .i_rd_reset_n(!xck_reset),
		.i_rd(!no_returns),
		.i_rdata({ ack_stb, err_stb, ret_wb_data }),
		.o_rd_empty(no_returns));

	initial	{ o_wb_ack, o_wb_err } = 2'b00;
	always @(posedge i_wb_clk)
	if (i_reset || bus_abort || !o_wb_cyc || no_returns || o_wb_err)
		{ o_wb_ack, o_wb_err } =  2'b00;
	else
		{ o_wb_ack, o_wb_err } = { ack_stb, err_stb };

	always @(posedge i_wb_clk)
		o_wb_data <= ret_wb_data;

endmodule
