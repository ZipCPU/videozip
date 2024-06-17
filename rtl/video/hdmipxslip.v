////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/hdmipxslip.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Control bit-slip.  This is necessary because many ISERDES
//		primitives will lock on a position which may (or may not) be
//	lined up with the associated clock.  This will allow us to adjust
//	the alignment.  While Xilinx offers a bit-slip capability within its
//	ISERDES, 1) it's hard to tell after the fact what slip you chose,
//	2) it's not necessarily repeatable, 3) it's not portable, and 4) I
//	like having control of what's going on within my designs.
//
//	Used only for manual pixel synchronization.
//
// Algorithm:
//	The algorithm works by creating three copies of the incoming data,
//	{ oldest, last, newest }, and shifting the result by the amount given.
//	This only works if the oldest bit is in the MSB position.
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
module	hdmipxslip #(
		parameter	WIDTH = 10,
		parameter	LGW = $clog2(3*WIDTH)
	) (
		// {{{
		input	wire			i_clk,
		input	wire	[LGW-1:0]	i_slip,
		input	wire	[WIDTH-1:0]	i_pixel,
		output	reg	[WIDTH-1:0]	o_pixel
		// }}}
	);

	// Register/wire declarations
	// {{{
	reg	[3*WIDTH-1:0]	last_pix;
	wire	[3*WIDTH-1:0]	w_this;
	// }}}

	always @(posedge i_clk)
		last_pix <= { last_pix[2*WIDTH-1:0], i_pixel };

	assign w_this = last_pix >> i_slip;

	always @(posedge i_clk)
		o_pixel <= w_this[9:0];

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	[19:0]	unused;
	assign	unused = w_this[29:10];
	// verilator lint_on  UNUSED
	// }}}
endmodule
