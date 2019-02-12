////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	mouseacc.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is the "mouse accumulator".  It's job is to take the mouse
//		motion information and accumulate it into a value bewteen zero
//	and a given limit.
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
module	mouseacc(i_clk, i_maxval, i_stb, i_mdata, o_loc);
	parameter	LOCBITS=10;
	localparam	LCLBITS=(LOCBITS<10)? 10:(LOCBITS+1);
	input	wire		i_clk;
	input	wire [(LOCBITS-1):0]	i_maxval;
	input	wire		i_stb;
	input	wire [9:0]		i_mdata;
	output	reg	[(LOCBITS-1):0]	o_loc;

	wire		m_dir = i_mdata[9];
	wire		m_ovfl= i_mdata[8];
	wire	[8:0]	m_val = (m_ovfl)? ((m_dir) ? 9'h101 : 9'h0ff)
				: { m_dir, i_mdata[7:0] };

	// The new mouse value is (apart from truncation) nominally given by the
	// old value plus the distance we traveled.
	wire	[(LCLBITS-1):0]	sum_val = { {(LCLBITS-LOCBITS){1'b0}}, o_loc }
					+ { {(LCLBITS-9){m_val[8]}},m_val };

	// Start the mouse on a valid value, the edge/corner
	initial	o_loc = {(LOCBITS){1'b0}};
	always @(posedge i_clk)
		if (i_stb)
		begin
			if ((sum_val[(LCLBITS-1)])
				||(sum_val>={{(LCLBITS-LOCBITS){1'b0}},i_maxval}))
				o_loc <= (m_dir)? 0:i_maxval;
			else
				o_loc <= sum_val[(LOCBITS-1):0];
		end
endmodule
