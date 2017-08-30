////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmipixelsync.v
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
`default_nettype	none
//
module	hdmipixelsync(i_clk, i_reset, i_px, o_sync, o_pix);
	input	wire		i_clk, i_reset;
	input	wire	[9:0]	i_px;
	output	wire	[4:0]	o_sync;
	output	reg	[9:0]	o_pix;

	reg	[18:0]	pre_match_win;
	wire	[18:0]	pre_pix;
	reg		lost_count, no_match;
	reg	[9:0]	pre_test, nxt_match;
	//
	reg		valid_match, last_valid, nxt_valid;
	reg	[3:0]	match_loc,   last_loc, r_match;

	always @(posedge i_clk)
		pre_match_win <= { pre_match_win[8:0], i_px };

	genvar	k;
	generate for(k=0; k<10; k=k+1)
		always @(posedge i_clk)
		begin
			pre_test[k] <= 1'b0;
			if((pre_match_win[(k+9):k]== 10'h0ab) // 354
				    ||(pre_match_win[(k+9):k]==10'h354) //0ab
				    ||(pre_match_win[(k+9):k]==10'h0aa) //154
				    ||(pre_match_win[(k+9):k]==10'h355))//2ab
				pre_test[k] <= 1'b1;

			// 2cc = 10_1100_1100 = 1011_0011_00 -> BREV = 0cd
			// 133 = 01_0011_0011 = 0100_1100_11 -> BREV = 332
			nxt_match[k] <= 1'b0;
			if((pre_match_win[(k+9):k]== 10'h0cd) // 2cc
				    ||(pre_match_win[(k+9):k]==10'h332))//133
				nxt_match[k] <= 1'b1;

		end
	endgenerate

	always @(posedge i_clk)
	begin
		valid_match <= (!i_reset);
		case(pre_test)
		10'h001: match_loc <= 4'h0;
		10'h002: match_loc <= 4'h1;
		10'h004: match_loc <= 4'h2;
		10'h008: match_loc <= 4'h3;
		10'h010: match_loc <= 4'h4;
		10'h020: match_loc <= 4'h5;
		10'h040: match_loc <= 4'h6;
		10'h080: match_loc <= 4'h7;
		10'h100: match_loc <= 4'h8;
		10'h200: match_loc <= 4'h9;
		default: valid_match <= 1'b0;
		endcase

		if (valid_match) // (last_valid)
		begin
			case(match_loc)
			4'h0: nxt_valid <= nxt_match[0];
			4'h1: nxt_valid <= nxt_match[1];
			4'h2: nxt_valid <= nxt_match[2];
			4'h3: nxt_valid <= nxt_match[3];
			4'h4: nxt_valid <= nxt_match[4];
			4'h5: nxt_valid <= nxt_match[5];
			4'h6: nxt_valid <= nxt_match[6];
			4'h7: nxt_valid <= nxt_match[7];
			4'h8: nxt_valid <= nxt_match[8];
			4'h9: nxt_valid <= nxt_match[9];
			default: nxt_valid <= 1'b0;
			endcase
		end else
			nxt_valid <= 1'b0;

		last_valid <= valid_match;
		last_loc   <= match_loc;
	end

	// Look for a string of 12 control characters, followed by a guard
	// character
	reg	[3:0]	match_count, found_loc;
	wire	[3:0]	chosen_match_loc;
	reg	sync_valid, found_valid;
	reg	[15:0]	lost_sync_counter;
	//
	always @(posedge i_clk)
		if ((i_reset)||(!valid_match))
			match_count <= 0;
		else if ((valid_match)&&(match_count < 4'hc))
			match_count <= match_count + 1'b1;
	always @(posedge i_clk)
		found_valid <= (!i_reset)&&(match_count == 4'hc)&&(nxt_valid);
	always @(posedge i_clk)
		if(nxt_valid)
			found_loc <= match_loc;


	// Declare no synch when ... we don't see anything for a long time
	always @(posedge i_clk)
		if (i_reset)
			lost_sync_counter <= 16'hffff;
		else if (found_valid)
			lost_sync_counter <= 0;
		else if (!(&lost_sync_counter))
			lost_sync_counter <= lost_sync_counter + 1'b1;

	always @(posedge i_clk)
		if (&lost_sync_counter)
			sync_valid <= 1'b0;
		else if (found_valid)
			sync_valid <= (found_loc == chosen_match_loc);

	validatecount	#(4) pixloc(i_clk, i_reset, found_valid, found_loc,
				chosen_match_loc);

	assign	o_sync = { (sync_valid), chosen_match_loc };
	assign	pre_pix = pre_match_win >> chosen_match_loc;

	always @(posedge i_clk)
		o_pix <= pre_pix[9:0];

endmodule
