////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmisync.v
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
module	hdmisync(i_pix_clk, i_reset,
		i_automatic_sync,
		i_logic_bitslip_r,
		i_logic_bitslip_g,
		i_logic_bitslip_b,
		i_r, i_g, i_b,
		o_r, o_g, o_b,
		o_manual_sync_word,
		o_automatic_sync_word,
		o_quality_sync_word);
	input	wire		i_pix_clk, i_reset;
	//
	input	wire		i_automatic_sync;
	input	wire	[4:0]	i_logic_bitslip_r;
	input	wire	[4:0]	i_logic_bitslip_g;
	input	wire	[4:0]	i_logic_bitslip_b;
	//
	input	wire	[9:0]	i_r, i_g, i_b;
	output	reg	[9:0]	o_r, o_g, o_b;
	//
	output	wire	[31:0]	o_manual_sync_word;
	output	wire	[31:0]	o_automatic_sync_word;
	output	wire	[31:0]	o_quality_sync_word;
	//
	//

	//
	//
	reg	[4:0]	lb_r, lb_g, lb_b;
	reg		dbg_and, dbg_or;
	wire	[9:0]	manual_r, manual_g, manual_b,
			auto_r,   auto_g,   auto_b;
	wire	[4:0]	auto_bitslip_r, auto_bitslip_g, auto_bitslip_b;

	//
	//
	hdmipixelsync	rasync(i_pix_clk, i_reset, i_r, auto_bitslip_r, auto_r);
	hdmipixelsync	gasync(i_pix_clk, i_reset, i_g, auto_bitslip_g, auto_g);
	hdmipixelsync	basync(i_pix_clk, i_reset, i_b, auto_bitslip_b, auto_b);

	//
	//
	// Apply a fixed bit synchronization, slipping bits until they look
	// "right" by hand.
	//
	hdmipxslip	rslip(i_pix_clk, i_logic_bitslip_r, i_r, manual_r);
	hdmipxslip	gslip(i_pix_clk, i_logic_bitslip_g, i_g, manual_g);
	hdmipxslip	bslip(i_pix_clk, i_logic_bitslip_b, i_b, manual_b);
//

	//
	reg	all_locked;
	always @(posedge i_pix_clk)
		all_locked <= ((auto_bitslip_r[4])
				&&(auto_bitslip_g[4])&&(auto_bitslip_b[4]));
	//
	assign	o_automatic_sync_word = { !i_automatic_sync, 6'h0, all_locked,
				3'h0, auto_bitslip_r, 3'h0, auto_bitslip_g,
				3'h0, auto_bitslip_b };
	assign	o_manual_sync_word = { i_automatic_sync, 7'h0,
			3'h0, i_logic_bitslip_r,
			3'h0, i_logic_bitslip_g,
			3'h0, i_logic_bitslip_b };
	assign	o_quality_sync_word = { dbg_and, dbg_or, 27'h0,
				auto_bitslip_r[4], auto_bitslip_g[4],
				auto_bitslip_b[4] };

	always @(posedge i_pix_clk)
		if (i_automatic_sync)
		begin
			o_r <= auto_r;
			o_g <= auto_g;
			o_b <= auto_b;
		end else begin
			o_r <= manual_r;
			o_g <= manual_g;
			o_b <= manual_b;
		end

	always @(posedge i_pix_clk)
		dbg_and <= (auto_bitslip_r[4])&&(auto_bitslip_g[4])
				&&(auto_bitslip_b[4]);
	always @(posedge i_pix_clk)
		dbg_or <= (auto_bitslip_r[4])||(auto_bitslip_g[4])
				||(auto_bitslip_b[4]);

endmodule
