////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiin.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
module	xhdmiin(i_clk, i_hsclk, i_ce, i_delay, o_delay,
			i_hs_wire, o_word);
	parameter	DC = 0;
	input	wire		i_clk;
	input	wire		i_hsclk;
	//
	input	wire		i_ce;
	input	wire	[4:0]	i_delay;
	output	wire	[4:0]	o_delay;
	input	wire	[1:0]	i_hs_wire;
	output	wire	[9:0]	o_word;

	wire		w_ignored;
	wire	[9:0]	w_word;

	wire	w_hs_wire, w_hs_delayed_wire;
	IBUFDS	hdmibuf(
			.I(i_hs_wire[1]), .IB(i_hs_wire[0]),
			.O(w_hs_wire));

	xhdmiin_deserdes the_deserdes(i_clk, i_hsclk,
		 i_ce, i_delay, o_delay, w_hs_wire, w_ignored, o_word);

endmodule
