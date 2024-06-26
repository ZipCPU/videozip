////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/xgenclk.v
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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
//
`default_nettype	none
//
// `define	DIFFERENTIAL
// }}}
module	xgenclk #(
		parameter	[0:0]	USE_PLL=1'b1
	) (
		// {{{
		input	wire		i_clk, i_hsclk, i_ce,
		input	wire	[7:0]	i_word,
`ifdef	DIFFERENTIAL
		inout	wire	[1:0]	io_pin,
`else
		inout	wire		io_pin,
`endif
		output	wire		o_clk,
		output	wire		o_locked
		// }}}
	);

	// Local declarations
	// {{{
	wire	[5:0]	ignored_data;
	wire	[1:0]	slave_to_master;

	wire	pll_input, w_pin, high_z; // fb_port;
	reg	[7:0]	r_word;

	always @(posedge i_clk)
		r_word <= i_word;
	// }}}

	// Verilator lint_off PINCONNECTEMPTY
	OSERDESE2	#(
		// {{{
		.DATA_RATE_OQ("DDR"), // DDR goes up to 950MHz, SDR only to 600
		.DATA_RATE_TQ("SDR"),
		.DATA_WIDTH(8),
		.SERDES_MODE("MASTER"),
		.TRISTATE_WIDTH(1)	// Really ... this is unused
		// }}}
	) lowserdes(
		// {{{
		.OCE(i_ce),
		.TCE(1'b1),	.TFB(), .TQ(high_z),
		.CLK(i_hsclk),	// HS clock
		.CLKDIV(i_clk),	// Divided clock input (lowspeed clock)
		.OQ(w_pin),	// Data path to IOB *only*
		.OFB(),	// Data path output feedback to ISERDESE2 or ODELAYE2
		.D1(r_word[7]),
		.D2(r_word[6]),
		.D3(r_word[5]),
		.D4(r_word[4]),
		.D5(r_word[3]),
		.D6(r_word[2]),
		.D7(r_word[1]),
		.D8(r_word[0]),
		.RST(1'b0), // .RST(!r_ce[1]),
		.TBYTEIN(1'b0), .TBYTEOUT(),
		.T1(1'b0), .T2(1'b0), .T3(1'b0), .T4(1'b0),
		.SHIFTIN1(), .SHIFTIN2(),
		.SHIFTOUT1(), .SHIFTOUT2()
		// }}}
	);
	// Verilator lint_on  PINCONNECTEMPTY

	// The I/O buffer / pin driver
	// {{{
`ifdef	DIFFERENTIAL
	IOBUFDS	genclkio(.I(w_pin), .IO(io_pin[0]), .IOB(io_pin[1]),
			.O(pll_input), .T(high_z));
`else
	IOBUF	genclkio(.I(w_pin), .IO(io_pin), .O(pll_input), .T(high_z));
`endif
	// }}}

	generate if (USE_PLL)
	begin : GEN_PLL
		// {{{
		reg	[5:0]	r_locked;
		wire	pll_fb, pll_fb_unbuffered, pll_locked, pll_output;

		// Verilator lint_off  PINCONNECTEMPTY
		PLLE2_BASE	#(
			// {{{
			.BANDWIDTH("LOW"),
			.CLKFBOUT_MULT(32),	// 800 MHz
			.CLKFBOUT_PHASE(0),
			.CLKIN1_PERIOD(25),	//  40 MHz
			.CLKOUT0_DIVIDE(16),
			.REF_JITTER1(0.19)	// Sim only parameter
			// }}}
		) pll (
			// {{{
			// .CLKOUT5_DIVIDE(1),
			.CLKFBIN(pll_fb),
			.CLKFBOUT(pll_fb),
			.CLKIN1(pll_input),
			// .CLKIN1(io_pin),
			.LOCKED(pll_locked),
			.PWRDWN(!i_ce),
			.RST(1'b0),
			.CLKOUT0(pll_output),
			.CLKOUT1(),
			.CLKOUT2(),
			.CLKOUT3(),
			.CLKOUT4(),
			.CLKOUT5()
			// }}}
		);
		// Verilator lint_on  PINCONNECTEMPTY


		// BUFG fbkbuf(.I(pll_fb_unbuffered), .O(pll_fb));
		BUFG pllbuf(.I(pll_output), .O(o_clk));

		initial	r_locked = 0;
		always @(posedge i_clk)
		begin
			r_locked[4:0] <= { r_locked[3:0], pll_locked };
			r_locked[5] <= i_ce && (&r_locked[4:2]);
		end

		assign	o_locked = r_locked[5];
		// }}}
	end else begin : NO_PLL
		// {{{
		assign	o_locked = 1'b0;
		BUFG clkbuf(.I(io_pin), .O(o_clk));
		// }}}
	end endgenerate

endmodule
