////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbcrossclk.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To cross clock domains with a (pipelined) wishbone bus.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
	always	@(posedge i_wb_clk)
		our_cyc <= ((our_cyc)&&(i_wb_cyc))||(i_wb_stb);

	initial	{ bus_abort, bus_abort_pipe } = -1;
	always	@(posedge i_wb_clk)
	if (i_reset)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (!i_wb_cyc && !ack_fifo_empty)
		{ bus_abort, bus_abort_pipe } <= -1;
	else if (ack_fifo_empty)
		{ bus_abort, bus_abort_pipe } <= { bus_abort_pipe, 1'b0 };

	initial	{ xck_reset, xck_reset_pipe } = -1;
	always	@(posedge i_xck or posedge i_reset)
	if (i_reset)
		{ xck_reset, xck_reset_pipe } <= 3'b111;
	else
		{ xck_reset, xck_reset_pipe[1] } <= xck_reset_pipe;

	always @(posedge i_wb_clk)
	if ((i_wb_stb)&&(!o_wb_stall))
		req_head <= req_head+1'b1;
	always @(posedge i_wb_clk)
		o_wb_stall <= (req_head != wb_ack_tail)&&(wb_ack_tail - req_head< THRESHOLD);

	initial	full_fifo_wptr = 0;
	always @(posedge i_wb_clk)
	if (i_reset || !i_wb_cyc)
	begin
		master_wrptr <= 0;
		master_rdptr <= 0;
	end else case(i_wb_stb && !o_wb_stall && !in_reset, !ack_fifo_empty })
	2'b10: master_wrptr <= master_wrptr + 1;
	2'b01: master_rdptr <= master_rdptr - 1;
	default: begin end
	endcase

	always @(*)
		o_wb_stall = (master_full || bus_abort);

	always @(*)
	master_full = (master_wrptr[LGFIFO-1:0] == master_rdptr[LGFIFO-1:0])
		&&(master_wrptr[LGFIFO] != master_rdptr[LGFIFO]);

	always @(posedge i_wb_clk)
	if (i_wb_stb && !master_full)
		req_fifo[master_wrptr] <= {
				i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };

	initial	ack_enable = 1'b0;
	always @(posedge i_wb_clk)
		ack_enable <= (i_wb_cyc && !bus_abort) && (!master_empty);

	initial pre_err = 0;
	always @(posedge i_wb_clk)
		{ pre_err, o_wb_data } <= ack_fifo[master_rdptr];

	always @(*)
	if (ack_enable)
		{ o_wb_ack, o_wb_err } =  { !pre_err, pre_err };
	else
		{ o_wb_ack, o_wb_err } = 2'b00;


	//
	//
	// On the cross wishbone clock ...
	//
	//	 De-queue the request, and issue it to the peripheral
	//
	always @(posedge i_xck)
	if (xck_reset)
		o_xclk_cyc <= 1'b0;
	else if (!xck_req_empty)
		o_xclk_cyc <= 1'b1;
	else if (xck_ack_empty)
		o_xclk_cyc <= 1'b0;

	always @(posedge i_xck)
	if (xck_reset)
	begin
		xck_rdptr <= 0;
		xck_wrptr <= 0;
	end else begin
		if (!xck_req_empty && (!o_xck_stb || !i_xck_stall))
			xck_rd_ptr <= xck_rd_ptr + 1;
		if (i_xck_ack || i_xck_err)
			xck_wr_ptr <= xck_wr_ptr + 1;
	end

	always @(posedge i_xck)
		o_xck_stb = !xck_req_empty;

	always @(posedge i_xck)
	if (!o_xck_stb || i_xck_stall)
		{ o_xck_we, o_xck_addr, o_xck_data, o_xck_sel }
			= req_fifo[xck_rd_ptr];

	always @(posedge i_xck)
	if (i_xck_ack || i_xck_err)
		ack_fifo[xck_wr_ptr] <= { i_xck_err, i_xck_data };


	//
	//
	// On the cross wishbone clock ...
	//
	//	 FIFO/queue up any returns to the FIFO
	//
	always @(posedge i_xclk_clk)
		if (i_xclk_ack)
			ack_head <= ack_head + 1'b1;
	always @(posedge i_xclk_clk)
		ack_fifo[ack_head] <= { i_xclk_err, i_xclk_data };

	// That then allows us to do everything else
	tfrvalue #(.NB(LGFIFO),.METHOD("FLAGGED")) tfr_ackptr(i_wb_clk,
		ack_head, i_xclk_clk, wb_ack_head);
	always @(posedge i_wb_clk)
		o_wb_ack <= (wb_ack_head != wb_ack_tail);
	always @(posedge i_wb_clk)
		if (wb_ack_head != wb_ack_tail)
			wb_ack_tail <= wb_ack_tail + 1'b1;
	always @(posedge i_wb_clk)
		o_wb_ack <= (wb_ack_head != wb_ack_tail);
	always @(posedge i_wb_clk)
		{ o_wb_err, o_wb_data } <= ack_fifo[wb_ack_tail];

endmodule
