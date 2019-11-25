////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmihist.v
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
module	hdmihist(i_wb_clk, i_hclk, i_pps, i_hdmi_r, i_hdmi_g, i_hdmi_b,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
		o_wb_stall, o_wb_ack, o_wb_data);
	input	wire		i_wb_clk, i_hclk, i_pps;
	input	wire	[9:0]	i_hdmi_r, i_hdmi_g, i_hdmi_b;
	// Wishbone inputs
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[1:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	// WB outputs
	output	wire		o_wb_stall;
	output	reg		o_wb_ack;
	output	reg	[31:0]	o_wb_data;


	// Process wishbone input(s)
	reg	[9:0]	r_match_r, r_match_g, r_match_b;
	initial	r_match_r = 10'h0;
	initial	r_match_g = 10'h0;
	initial	r_match_b = 10'h0;
	always @(posedge i_wb_clk)
	begin
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr[1:0] == 2'b00))
		begin
			r_match_r <= i_wb_data[29:20];
			r_match_g <= i_wb_data[19:10];
			r_match_b <= i_wb_data[ 9: 0];
		end
	end

	//
	// Transfer the clock pulse from the i_wb_clk domain to the i_hclk
	// domain.  Note that this will destroy the absolute timing reference
	// of the clock, but that really shouldn't be too much of a problem
	// since we really aren't all that concerned with GPS seconds accuracy,
	// only having a once per (about a) second strobe.
	reg	[5:0]	clk_transfer;
	always @(posedge i_wb_clk)
		clk_transfer <= { clk_transfer[4:0], i_pps };

	reg		slow_pps;
	always @(posedge i_wb_clk)
		slow_pps <= (clk_transfer != 6'h0);

	reg	[2:0]	hs_pps_transfer;
	reg		r_hs_pps;
	always @(posedge i_hclk)
		hs_pps_transfer <= { hs_pps_transfer[1:0], slow_pps };
	always @(posedge i_hclk)
		r_hs_pps <= (!hs_pps_transfer[2])&&(hs_pps_transfer[1]);

	reg	hs_r_inc, hs_g_inc, hs_b_inc;
	always @(posedge i_hclk)
		hs_r_inc <= (i_hdmi_r == r_match_r);
	always @(posedge i_hclk)
		hs_g_inc <= (i_hdmi_g == r_match_g);
	always @(posedge i_hclk)
		hs_b_inc <= (i_hdmi_b == r_match_b);

	// Count how many times we match against the given count value
	reg	[31:0]	hs_r_cnt, hs_g_cnt, hs_b_cnt;

	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_r_cnt <= 0;
		else 
			hs_r_cnt <= hs_r_cnt + { {(31){1'b0}}, hs_r_inc };

	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_g_cnt <= 0;
		else
			hs_g_cnt <= hs_g_cnt + { {(31){1'b0}}, hs_g_inc };

	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_b_cnt <= 0;
		else
			hs_b_cnt <= hs_b_cnt + { {(31){1'b0}}, hs_b_inc };

	// Transfer these count registers to something that can cross clock
	// domains
	reg	[31:0]	hs_r_out, hs_g_out, hs_b_out;
	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_r_out <= hs_r_cnt;
	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_g_out <= hs_g_cnt;
	always @(posedge i_hclk)
		if (r_hs_pps)
			hs_b_out <= hs_b_cnt;

	// Now, let's handle our wishbone outputs
	always @(posedge i_wb_clk)
	case(i_wb_addr)
	2'b00: o_wb_data <= { 2'h0, r_match_r, r_match_g, r_match_g };
	2'b01: o_wb_data <= hs_r_out;
	2'b10: o_wb_data <= hs_g_out;
	2'b11: o_wb_data <= hs_b_out;
	endcase

	initial	o_wb_ack = 1'b0;
	always @(posedge i_wb_clk)
		o_wb_ack <= i_wb_stb;

	assign	o_wb_stall = 1'b0;

endmodule
