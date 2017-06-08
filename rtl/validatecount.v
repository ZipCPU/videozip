////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	validatecount.v
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
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
// `define	BYPASS_TEST
//
module	validatecount(i_clk, i_reset, i_v, i_val, o_val);
	parameter	NBITS=16;
	input	wire	i_clk, i_reset, i_v;
	input	wire	[(NBITS-1):0]	i_val;
	output	reg	[(NBITS-1):0]	o_val;

`ifdef	BYPASS_TEST
	always @(posedge i_clk)
		if (i_v)
			o_val <= i_val;
`else
	reg			inc, dec;
	reg	[2:0]		ngood;
	reg	[(NBITS-1):0]	r_val;

	reg	r_eq, no_val, r_v;

	always @(posedge i_clk)
		r_v <= i_v;

	always @(posedge i_clk)
		r_eq <= (i_val == r_val);

	always @(posedge i_clk)
		no_val <= (ngood == 0);

	always @(posedge i_clk)
		if ((r_v)&&(no_val))
			r_val <= i_val;


	initial	inc = 1'b0;
	initial	dec = 1'b0;
	always @(posedge i_clk)
	begin
		inc  <= (!i_reset)&&(r_v)&&((r_eq)||(no_val));
		dec  <= (!i_reset)&&(r_v)&&(!r_eq);
	end

	initial	ngood = 0;
	always @(posedge i_clk)
		if (i_reset)
			ngood <= 0;
		else if ((inc)&&(!(&ngood)))
			ngood <= ngood + 1'b1;
		else if ((dec)&&(ngood != 0))
			ngood <= ngood - 1'b1;
	always @(posedge i_clk)
		if (&ngood)
			o_val <= r_val;
		else if (ngood == 0)
			o_val <= 0;
`endif

endmodule
