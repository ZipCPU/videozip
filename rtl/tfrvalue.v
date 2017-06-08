////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tfrvalue.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Transfer an incrementing value, such as a FIFO's read or
//		write pointers, from one clock to another--such as from a write
//	clock to a read clock or vice versa.
//
//	We'll use a gray code to do the transfer, ensuring that any mistakes
//	in value transfer end up one above or one below the true value.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
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
module	tfrvalue(i_aclk, i_value, i_bclk, o_value);
	parameter	NB = 16;
	parameter	METHOD = "GRAYCODE";
	input	wire			i_aclk, i_bclk;
	input	wire	[(NB-1):0]	i_value;
	output	wire	[(NB-1):0]	o_value;

/*
	genvar	k, j;
	generate
	if (METHOD == "GRAYCODE")
	begin
		// Convert the input to gray code
		reg	[(NB-1):0]	r_agray, q_bgray, r_bgray, r_value;

		always @(posedge i_aclk)
			r_agray <=  { 1'b0, i_value[(NB-1):1] } ^ i_value[(NB-1):0];

		always @(posedge i_bclk)
			q_bgray <= r_agray;

		always @(posedge i_bclk)
			r_bgray <= q_bgray;

		always @(posedge i_bclk)
		begin
			for(k=0; k<NB; k=k+1)
			begin
				r_value[k] = r_bgray[k];
				for(j=k+1; j<NB; j=j+1)
					r_value[k] = r_value[k] ^ r_bgray[j];
			end
		end
	end else if (METHOD == "FLAGGED")
	begin
*/

		reg			r_atfr, q_tfr, r_btfr;
		reg			r_aack, q_ack, r_back;
		reg	[(NB-1):0]	r_aval, r_value;
		always @(posedge i_aclk)
			if ((!r_atfr)&&(!r_aack))
			begin
				r_aval <= i_value;
				if (i_value != r_aval)
					r_atfr <= 1'b1;
			end else if (r_aack)
				r_atfr <= 1'b0;


		always @(posedge i_bclk)
			q_tfr <= r_atfr;
		always @(posedge i_bclk)
			r_btfr <= q_tfr;

		always @(posedge i_bclk)
			if ((r_btfr)&&(!r_back))
			begin
				r_value <= r_aval;
				r_back <= 1'b1;
			end else if (!r_btfr)
				r_back <= 1'b0;

		always @(posedge i_aclk)
			q_ack <= r_back;
		always @(posedge i_aclk)
			r_aack <= q_ack;

		assign	o_value = i_value;
/*
	end else
		assign	o_value = i_value;
	endgenerate
*/
		
endmodule
