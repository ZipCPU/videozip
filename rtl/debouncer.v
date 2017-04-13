////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	debouncer.v
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
module	debouncer(i_clk, i_in, o_debounced);
	parameter	NIN=16+5, LGWAIT=17;
	input	wire			i_clk;
	input	wire	[(NIN-1):0]	i_in;
	output	reg	[(NIN-1):0]	o_debounced;

	reg	[(NIN-1):0]	r_in, q_in;
	always @(posedge i_clk)
		q_in <= i_in;
	always @(posedge i_clk)
		r_in <= q_in;

	reg	[(NIN-1):0]	r_last;

	// Here's how we do this ... 
	//	When idle and anything changes, set the new value and a timer
	//		While the timer is active, respond to nothing.
	//	When timer is idle see #1 above
	reg	[(LGWAIT-1):0]	timer;
	initial	timer = { (LGWAIT){1'b1}  };
	initial	o_debounced = { (NIN) {1'b0} };
	always @(posedge i_clk)
		if (r_last != r_in)
		begin
			timer <= {(LGWAIT){1'b1}};
			r_last <= r_in;
		end else if (timer == 0)
			o_debounced <= r_last;
		else
			timer <= timer - 1'b1;

endmodule
