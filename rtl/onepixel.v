////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	onepixel.v
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
module	onepixel(i_wb_clk, i_data_clk,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
			o_wb_ack, o_wb_stall, o_wb_data,
		i_data);
	input	wire	i_wb_clk, i_data_clk;
	// Wishbone bus inputs
	input	wire	i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	output	reg	o_wb_ack;
	output	wire	o_wb_stall;
	output	reg	[31:0]	o_wb_data;
	//
	input	[31:0]	i_data;


	reg	[31:0]	r_wb_delay_counter,r_data_delay_counter,q_delay_counter;
	reg	[31:0]	counter;
	reg		zcounter;	// Separate counter from data by one clk
	reg	[31:0]	r_data_captured, q_data_captured, wb_data_captured;

	always @(posedge i_wb_clk)
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr == 1'b0))
			r_wb_delay_counter <= i_wb_data;

	always @(posedge i_data_clk)
		q_delay_counter <= r_wb_delay_counter;
	always @(posedge i_data_clk)
		r_data_delay_counter <= q_delay_counter;

	always @(posedge i_data_clk)
		if (counter == r_data_delay_counter)
			r_data_delay_counter <= 0;
		else
			r_data_delay_counter <= r_data_delay_counter + 1'b1;

	always @(posedge i_data_clk)
		zcounter <= (counter == 0);

	always @(posedge i_data_clk)
		if (zcounter)
			r_data_captured <= i_data;
	always @(posedge i_data_clk)
		q_data_captured <= r_data_captured;
	always @(posedge i_data_clk)
		wb_data_captured <= q_data_captured;

	always @(posedge i_wb_clk)
		o_wb_data <= (i_wb_addr) ? wb_data_captured :r_wb_delay_counter;
	always @(posedge i_wb_clk)
		o_wb_ack <= i_wb_stb;

endmodule

