////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmipxslip
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
module	hdmipxslip(i_clk, i_slip, i_pixel, o_pixel);
	input	wire		i_clk;
	input	wire	[4:0]	i_slip;
	input	wire	[9:0]	i_pixel;
	output	reg	[9:0]	o_pixel;

	reg	[29:0]	last_pix;
	wire	[29:0]	w_this;

	always @(posedge i_clk)
		last_pix <= { last_pix[19:0], i_pixel };

	assign w_this = last_pix >> i_slip;

	always @(posedge i_clk)
		o_pixel <= w_this[9:0];

	// verilator lint_off UNUSED
	wire	[19:0]	unused;
	assign	unused = w_this[29:10];
	// verilator lint_on  UNUSED
endmodule
