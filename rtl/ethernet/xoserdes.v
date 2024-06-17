////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/xoserdes.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This module works in conjunction with the genclk module to
//		generate  clock with an arbitrary frequency.  The genclk
//	module creates an 8-bit word, and this module sends that word to a
//	clock capable output pin.  The pin does not need to be connected
//	to anything on your board, but it does likely need to be a clock
//	capable pin.
//
//	There are two parts to the module:
//
//	A. Output at 8x speed to the pin
//	B. Read back in from the pin (actually from the feedback port of
//		the output serdes), and run the newly created clock into
//		a PLL to clean it up.
//
//	The module is nominally designed for a 100MHz clock input.  Using a
//	100 MHz clock input, the maximum clock speed that can be created is
//	about 166MHz.
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
module	xoserdes (
		// {{{
		input	wire		i_clk, i_areset,
		input	wire		i_hsclk,
		input	wire	[3:0]	i_word,
		output	wire		io_pin
		// }}}
	);

	// Local decalarations
	// {{{
	wire		w_pin; // fb_port;
	reg	[1:0]	reset_pipe;
	reg		sync_reset;
	// }}}

	// sync_reset, reset_pipe
	// {{{
	initial	{ sync_reset, reset_pipe } <= -1;
	always @(posedge i_clk or posedge i_areset)
	if (i_areset)
		{ sync_reset, reset_pipe } <= -1;
	else
		{ sync_reset, reset_pipe } <= { reset_pipe, 1'b0 };
	// }}}

	// Verilator lint_off PINCONNECTEMPTY
	OSERDESE2	#(
		// {{{
		.DATA_RATE_OQ("DDR"),
		.DATA_RATE_TQ("BUF"),
		.TRISTATE_WIDTH(1),
		.DATA_WIDTH(4),
		.SERDES_MODE("MASTER")
		// }}}
	) oserdes(
		// {{{
		.OCE(1'b1),
		.TCE(1'b1),	.TFB(), .TQ(),
		.CLK(i_hsclk),	// HS clock
		.CLKDIV(i_clk),	// Divided clock input (lowspeed clock)
		.OQ(w_pin),	// Data path to IOB *only*
		.OFB(),		// Data path output feedback to ISERDESE2 or ODELAYE2
		.D1(i_word[3]),
		.D2(i_word[2]),
		.D3(i_word[1]),
		.D4(i_word[0]),
		.D5(),
		.D6(),
		.D7(),
		.D8(),
		.RST(sync_reset), // .RST(!r_ce[1]),
		.TBYTEIN(1'b0), .TBYTEOUT(),
		.T1(1'b0), .T2(1'b0), .T3(1'b0), .T4(1'b0),
		.SHIFTIN1(), .SHIFTIN2(),
		.SHIFTOUT1(), .SHIFTOUT2()
		// }}}
	);
	// Verilator lint_on  PINCONNECTEMPTY

	OBUF	u_obuf(.I(w_pin), .O(io_pin));
endmodule
