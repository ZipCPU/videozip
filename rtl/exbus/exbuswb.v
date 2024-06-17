////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exbuswb.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is the top level component for the exbus when attached
//		to a Wishbone bus.
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
module	exbuswb #(
		// {{{
		parameter	ADDRESS_WIDTH=30,	// Width in log2(words)
		localparam	AW=ADDRESS_WIDTH, // Shorthand for address width
			DW=32,			// Shorthand for bus data width
		parameter	LGFIFO = 5	// Log_2(FIFO Depth)
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		output	wire			o_reset,
		// The input channel from the serial port
		// {{{
		input	wire			i_rx_stb,
		input	wire	[7:0]		i_rx_byte,
		// }}}
		// The return serial port channel
		// {{{
		output	reg			o_tx_stb,
		output	reg	[7:0]		o_tx_byte,
		input	wire			i_tx_busy,
		// }}}
		// GPIO interface
		// {{{
		input	wire	[1:0]		i_gpio,
		output	reg	[1:0]		o_gpio,
		// }}}
		// Console interface
		// {{{
		input	wire			i_console_stb,
		input	wire	[6:0]		i_console_byte,
		output	wire			o_console_busy,
		//
		output	reg			o_console_stb,
		output	reg	[6:0]		o_console_byte,
		// }}}
		// Wishbone
		// {{{
		output	wire			o_wb_cyc,
		output	wire			o_wb_stb,
		output	wire			o_wb_we,
		output	wire	[(AW-1):0]	o_wb_addr,
		output	wire	[DW-1:0]	o_wb_data,
		output	wire	[DW/8-1:0]	o_wb_sel,
		// Wishbone inputs
		input	wire			i_wb_stall, i_wb_ack, i_wb_err,
		input	wire	[DW-1:0]	i_wb_data,
		// }}}
		input	wire			i_interrupt
		// }}}
	);

	// Local declarations
	// {{{
	localparam	CW=35;	// Command word width
	wire			rx_busy;
	wire			iword_stb, cmd_reset, iword_busy,
				ign_iword_active;
	wire	[CW-1:0]	iword_data;
	wire			in_stb, in_busy, ign_in_active;
	wire	[CW-1:0]	in_data;
	wire	[LGFIFO:0]	ign_in_fill;
	wire			bus_rd_busy;
	wire			ififo_valid, ififo_empty, ififo_full;
	reg			ififo_err;
	wire	[CW-1:0]	ififo_data;
	wire			ofifo_valid, ofifo_empty, ofifo_full;
	reg			ofifo_err;
	wire	[LGFIFO:0]	ign_ofifo_fill;
	wire	[CW-1:0]	ofifo_data;
	wire			compress_valid, compress_busy, compress_active;
	wire	[CW-1:0]	compress_data;
	wire			idle_valid, idle_busy, idle_last;
	wire	[CW-1:0]	idle_data;
	wire			deword_valid, deword_busy, ign_deword_last;
	wire	[6:0]		deword_byte, null_byte;
	wire			bus_stb;
	wire	[CW-1:0]	bus_word;
	wire			out_busy;

	// }}}

	// o_console_stb, o_console_byte
	// {{{
	initial	o_console_stb = 1'b0;
	always @(posedge i_clk)
	begin
		o_console_stb  <= (i_rx_stb && !i_rx_byte[7]);
		o_console_byte <= i_rx_byte[6:0];
	end
	// }}}

	// exmkword: iword_stb, iword_data, cmd_reset
	// {{{
	exmkword
	mkword(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_sync(1'b0),
		.i_stb(i_rx_stb && i_rx_byte[7]), .o_busy(rx_busy),
			.i_data(i_rx_byte[6:0]),
		.o_stb(iword_stb), .i_busy(iword_busy),
			.o_data(iword_data),
		.o_reset_bridge(cmd_reset),
		.o_reset_design(o_reset),
		.o_active(ign_iword_active)
		// }}}
	);
	// }}}

	// exdecompress: iword_* -> in_stb, in_data
	// {{{
	exdecompress
	decompress(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(iword_stb), .o_busy(iword_busy),
			.i_word(iword_data),
		.o_stb(in_stb), .i_busy(in_busy),
			.o_word(in_data),
		.o_active(ign_in_active)
		// }}}
	);
	// }}}

	// exfifo: Incoming FIFO, in_* -> ififo_data, ififo_valid, ififo_err
	// {{{
	exfifo #(
		// {{{
		.BW(CW), .LGFLEN(LGFIFO)
		// }}}
	) ififo(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_wr(in_stb), .i_data(in_data), .o_full(ififo_full),
			.o_fill(ign_in_fill),
		.i_rd(!bus_rd_busy), .o_data(ififo_data),
			.o_empty(ififo_empty)
		// }}}
	);

	assign	in_busy = ififo_full;

	assign	ififo_valid = !ififo_empty;
	always @(posedge i_clk)
	if (i_reset || cmd_reset)
		ififo_err <= 1'b0;
	else if (i_rx_stb && i_rx_byte[7] && rx_busy)
		ififo_err <= 1'b1;
	// }}}

	// o_gpio
	// {{{
	always @(posedge i_clk)
	if (i_reset || cmd_reset)
		o_gpio <= 2'b00;
	else if (ififo_valid && !bus_rd_busy && ififo_data[34:33] == 2'b11)
		o_gpio <= ififo_data[32:31];
	// }}}

	// exwb: Drive the bus: ififo_* -> Wishbone -> bus_stb, bus_word
	// {{{
	exwb #(
		.ADDRESS_WIDTH(AW)
	) genbus(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		// Requests
		.i_cmd_stb(ififo_valid),
			.i_cmd_word(ififo_data),
			.o_cmd_busy(bus_rd_busy),
		// Results
		.o_cmd_stb(bus_stb), .o_cmd_word(bus_word),
		// Wishbone
		.o_wb_cyc(o_wb_cyc), .o_wb_stb(o_wb_stb), .o_wb_we(o_wb_we),
			.o_wb_addr(o_wb_addr), .o_wb_data(o_wb_data),
			.o_wb_sel(o_wb_sel),
		.i_wb_stall(i_wb_stall), .i_wb_ack(i_wb_ack),
			.i_wb_data(i_wb_data), .i_wb_err(i_wb_err)
		// }}}
	);
	// }}}

	// exfifo: Outgoing FIFO, bus_* -> ofifo_data, ofifo_valid, ofifo_err
	// {{{
	exfifo #(
		// {{{
		.BW(35), .LGFLEN(LGFIFO)
		// }}}
	) ofifo(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		//
		.i_wr(bus_stb), .i_data(bus_word),
			.o_full(ofifo_full), .o_fill(ign_ofifo_fill),
		//
		.i_rd(!compress_busy), .o_data(ofifo_data),
			.o_empty(ofifo_empty)
		// }}}
	);

	assign	ofifo_valid = !ofifo_empty;
	always @(posedge i_clk)
	if (i_reset || cmd_reset)
		ofifo_err <= 1'b0;
	else if (bus_stb && ofifo_full)
		ofifo_err <= 1'b1;
	// }}}

	// excompress: idle_*, compress_valid, compress_data, compress_active
	// {{{
	excompress
	compress(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(ofifo_valid), .i_word(ofifo_data),
			.o_busy(compress_busy),
		.o_stb(compress_valid), .o_word(compress_data),
			.i_busy(idle_busy),
		.o_active(compress_active)
		// }}}
	);
	// }}}

	// exidle: ofifo* -> idle_valid, idle_data
	// {{{
	exidle #(
		.OPT_IDLE(1'b1)
	) idle(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),
		.i_stb(compress_valid), .i_word(compress_data),
			.i_last(1'b0), .o_busy(idle_busy),
			.o_null(null_byte),
		.i_aux(i_gpio), .i_cts(1'b1), .i_int(i_interrupt),
			.i_fifo_err(ofifo_err || ififo_err),
		.o_stb(idle_valid), .o_word(idle_data),
			.o_last(idle_last), .i_busy(deword_busy)
		// }}}
	);
	// }}}

	// exdeword: -> deword_valid, deword_byte
	// {{{
	exdeword
	deword(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || cmd_reset),//.i_gpio(i_gpio),
		.i_stb(idle_valid), .i_word(idle_data), .i_last(idle_last),
			.o_busy(deword_busy),
		.o_stb(deword_valid), .i_busy(out_busy),
			.o_byte(deword_byte), .o_last(ign_deword_last)
		// }}}
	);
	// }}}

	// out_busy
	// {{{
	assign	out_busy = (o_tx_stb && i_tx_busy) || i_console_stb;
	// }}}

	// o_tx_stb
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		o_tx_stb <= 1'b0;
	else if (!o_tx_stb || !i_tx_busy)
		o_tx_stb <= i_console_stb || deword_valid;
	// }}}

	// o_tx_byte
	// {{{
	always @(posedge i_clk)
	if (!o_tx_stb || !i_tx_busy)
	begin
		if (i_console_stb)
			o_tx_byte <= { 1'b0, i_console_byte };
		else
			o_tx_byte <= { 1'b1, deword_byte };
	end
	// }}}

	assign	o_console_busy = o_tx_stb && i_tx_busy;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, null_byte, idle_last, compress_active,
			ign_in_active, ign_in_fill, ign_ofifo_fill,
			ign_iword_active, ign_deword_last };
endmodule
