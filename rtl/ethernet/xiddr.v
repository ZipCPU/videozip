////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xiddr.v
//
// Project:	OpenArty, an entirely open SoC based upon the Arty platform
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018-2019, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
module	xiddr(i_clk, i_pin, o_v);
	input	wire		i_clk;
	input	wire		i_pin;
	output	wire	[1:0]	o_v;

	IDDR #(
		.DDR_CLK_EDGE("SAME_EDGE_PIPELINED"),
		.SRTYPE("SYNC")
	) IDDRi(
		.C(i_clk),
		//
		.R(1'b0),
		.S(1'b0),
		.CE(1'b1),
		//
		.D(i_pin),
		.Q1(o_v[0]),
		.Q2(o_v[1]));

endmodule
