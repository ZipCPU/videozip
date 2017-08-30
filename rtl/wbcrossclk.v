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
// Copyright (C) 2017, Gisselquist Technology, LLC
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
			o_wb_ack, o_wb_stall, o_wb_data, o_wb_err,
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
	reg	our_cyc;
	always	@(posedge i_wb_clk)
		our_cyc <= ((our_cyc)&&(i_wb_cyc))||(i_wb_stb);
	always @(posedge i_xclk_clk)
		tfr_cyc <= { tfr_cyc[(TFRCLOCKS-2):0], (our_cyc)||(i_wb_stb) };
	assign	o_xclk_cyc = tfr_cyc[(TFRCLOCKS-1)];

	always @(posedge i_wb_clk)
		if ((i_wb_stb)&&(!o_wb_stall))
			req_head <= req_head+1'b1;
	always @(posedge i_wb_clk)
		o_wb_stall <= (req_head != wb_ack_tail)&&(wb_ack_tail - req_head< THRESHOLD);

	always @(posedge i_wb_clk)
		req_fifo[req_head] <= {
				i_wb_we, i_wb_addr, i_wb_data, i_wb_sel };

	//
	//
	// On the cross wishbone clock ...
	//
	//	 De-queue the request, and issue it to the peripheral
	//
	// Find where the head is at, but on our clock
	tfrvalue #(.NB(LGFIFO),.METHOD("FLAGGED")) tfr_reqptr(i_wb_clk,
		req_head, i_xclk_clk, xclk_req_head);

	// That then allows us to do everything else
	wire	[(LGFIFO-1):0]	next_xclk_tail;
	assign	next_xclk_tail = xclk_tail + 1'b1;
	always @(posedge i_xclk_clk)
		if (!o_xclk_cyc)
			o_xclk_stb <= 1'b0;
		else if ((o_xclk_stb)&&(!i_xclk_stall))
			o_xclk_stb <= (next_xclk_tail != xclk_req_head);
		else
			o_xclk_stb <= (xclk_req_head != xclk_tail);
	always @(posedge i_xclk_clk)
		if ((o_xclk_stb)&&(!i_xclk_stall)&&(xclk_req_head != xclk_tail))
			xclk_tail <= xclk_tail + 1'b1;
	always @(posedge i_xclk_clk)
		xclk_fifo_data <= req_fifo[xclk_tail];

	assign	o_xclk_we   = xclk_fifo_data[(AW+DW+DW/8)];
	assign	o_xclk_addr = xclk_fifo_data[(AW+DW+DW/8-1):(DW+DW/8)];
	assign	o_xclk_data = xclk_fifo_data[(DW+DW/8-1):(DW/8)];
	assign	o_xclk_sel  = xclk_fifo_data[(DW/8-1):0];

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
