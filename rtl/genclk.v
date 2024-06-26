////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/genclk.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To generate a clock using digital logic, but one that switches
//		at the right speed overall.
//
//	This particular component takes the desired clock stepping word
//	(2^32 / desired_frequency) and uses it to generate a clock at the
//	desired_frequency rate.
//
//	The output itself is 8 steps of that clock, necessitating an 8x
//	output serdes to create a clock from this output word.  As a result,
//	the phase error on the output of this routine will be (at a maximum)
//	1/16th the duration of i_clk--allowing more flexibility in clock
//	generation.
//
//	If your goal is to create a slow clock, this may be all you need to
//	generate such a clock.  If you need to generate a high speed clock,
//	however, you may wish to run the output result into a PLL to clean
//	up any residual phase noise.
//
//
//	Maximum output clock speed is ... ?
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
`default_nettype	none
// }}}
module	genclk(i_clk, i_delay, o_word, o_stb);
	parameter	BW=32;		// The bus width
	localparam	UPSAMPLE=8;	// Upsample factor
	input	wire				i_clk;
	input	wire	[(BW-1):0]		i_delay;
	output	reg	[(UPSAMPLE-1):0]	o_word;
	output	reg				o_stb;

	reg	[(BW-1):0]	counter [0:(UPSAMPLE-1)];
	reg	[(BW-1):0] r_delay;

	reg	[(BW-1):0] times_three;
	reg	[(BW-1):0] times_five;
	reg	[(BW-1):0] times_seven;

	always @(posedge i_clk)
		times_three <= { i_delay[(BW-2):0], 1'b0 } + i_delay;

	always @(posedge i_clk)
		times_five  <= { i_delay[(BW-3):0], 2'b0 } + i_delay;

	always @(posedge i_clk)
		times_seven <= { i_delay[(BW-4):0], 3'b0 } - i_delay;

	always @(posedge i_clk)
		r_delay <= i_delay;

	//
	////////////////////////////////////////////////////////////////////////
	//

	always @(posedge i_clk)	// Times one
		counter[1] <= counter[0] + r_delay;

	always @(posedge i_clk)	// Times two
		counter[2] <= counter[0] + { r_delay[(BW-2):0], 1'b0 };

	always @(posedge i_clk) // Times three
		counter[3] <= counter[0] + times_three;

	always @(posedge i_clk) // Times four
		counter[4] <= counter[0] + { r_delay[(BW-3):0], 2'b0 };

	always @(posedge i_clk) // Times five
		counter[5]  <= counter[0] + times_five;

	always @(posedge i_clk)
		counter[6]  <= counter[0] + { times_three[(BW-2):0], 1'b0 };

	always @(posedge i_clk)
		counter[7] <= counter[0] + times_seven;

	always @(posedge i_clk) // Times eight---and generating the next clk wrd
		{ o_stb, counter[0] }  <= counter[0] + { r_delay[(BW-4):0], 3'h0 };

	always @(posedge i_clk)
		o_word <= {	// High order bit is "first"
			counter[1][(BW-1)],
			counter[2][(BW-1)],
			counter[3][(BW-1)],
			counter[4][(BW-1)],
			counter[5][(BW-1)],
			counter[6][(BW-1)],
			counter[7][(BW-1)],
			counter[0][(BW-1)]
		};
endmodule
