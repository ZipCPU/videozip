////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	crossclkparam.v
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
module	crossclkparam(i_a_clk, i_b_clk, i_params, o_params);
	parameter			PW=32;
	input	wire			i_a_clk, i_b_clk;
	input	wire	[(PW-1):0]	i_params;
	output	reg	[(PW-1):0]	o_params;

	reg	[1:0]	a_send, b_send, a_ack;
	reg	[(PW-1):0]	r_params;
	reg		b_ack;

	initial	a_send = 2'b00;
	initial	r_params = 0;
	always @(posedge i_a_clk)
		if ((a_send==2'b00)&&(!a_ack[1]))
		begin
			r_params <= i_params;
			a_send <= 2'b01;
		end else if (|a_send)
			a_send <= { a_send[0], !(|a_ack) };

	initial	b_send = 2'b00;
	always @(posedge i_b_clk)
		b_send <= { b_send[0], a_send[1] };

	initial	b_ack = 1'b0;
	always @(posedge i_b_clk)
		b_ack <= b_send[1];

	initial	a_ack = 2'b00;
	always @(posedge i_a_clk)
		a_ack <= { a_ack[0], b_ack };

	initial	o_params = 0;
	always @(posedge i_b_clk)
		if ((b_send[1])&&(!b_ack))
			o_params <= r_params;
endmodule
