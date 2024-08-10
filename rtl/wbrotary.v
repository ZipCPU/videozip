////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/wbrotary.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	"Decode" motor encoder counts
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module	wbrotary #(
		parameter			CW=32, NFF=2,
		parameter	[CW-1:0]	OPT_INCREMENT = 1
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Wishbone interface
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		// input wire		i_wb_addr
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	wire	[31:0]	o_wb_data,

		// Hardware decoder inputs
		input	wire		i_a, i_b
		// }}}
	);

	// Local declarations
	// {{{
	reg	[31:0]		new_counts;
	reg	[CW-1:0]	r_counts;
	reg	[(NFF-2):0]	apipe, bpipe;
	reg			ck_a, lst_a, ck_b, lst_b;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock synchronizers--synchronize our inputs to the system clock
	// {{{
	initial	{ lst_a, ck_a, apipe } = 0;
	always @(posedge i_clk)
		{ lst_a, ck_a, apipe } <= { ck_a, apipe, i_a };

	initial	{ lst_b, ck_b, bpipe } = 0;
	always @(posedge i_clk)
		{ lst_b, ck_b, bpipe } <= { ck_b, bpipe, i_b };
	// }}}
	//

	// new_counts, to handle i_wb_sel on write transactions
	// {{{
	always @(*)
	begin
		new_counts = 0;
		new_counts[CW-1:0] = r_counts;
		if (i_wb_sel[0]) new_counts[ 7: 0] = i_wb_data[ 7: 0];
		if (i_wb_sel[1]) new_counts[15: 8] = i_wb_data[15: 8];
		if (i_wb_sel[2]) new_counts[23:16] = i_wb_data[23:16];
		if (i_wb_sel[3]) new_counts[31:24] = i_wb_data[31:24];
	end
	// }}}

	// r_counts
	// {{{
	initial	r_counts = 0;
	always @(posedge i_clk)
	if (i_reset)
		// Tare the counter by setting it to zero on any reset
		r_counts <= 0;
	else begin
		case({lst_a, lst_b, ck_a, ck_b})
		4'h1: 	r_counts <= r_counts + OPT_INCREMENT;
		4'h7:	r_counts <= r_counts + OPT_INCREMENT;
		4'he:	r_counts <= r_counts + OPT_INCREMENT;
		4'h8:	r_counts <= r_counts + OPT_INCREMENT;
		//
		4'h4: 	r_counts <= r_counts - OPT_INCREMENT;
		4'hd:	r_counts <= r_counts - OPT_INCREMENT;
		4'hb:	r_counts <= r_counts - OPT_INCREMENT;
		4'h2:	r_counts <= r_counts - OPT_INCREMENT;
		default: begin end	// 0, 3, 5, 6, 9, a, c, f
		endcase

		if (i_wb_stb && !o_wb_stall && i_wb_we && i_wb_sel != 0)
			r_counts[CW-1:0] <= new_counts;
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone handling
	// {{{
	assign	o_wb_stall = 1'b0;

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_wb_ack <= 1'b0;
	else
		o_wb_ack <= (i_wb_stb && !o_wb_stall);

	assign	o_wb_data = r_counts;
	// }}}
endmodule
