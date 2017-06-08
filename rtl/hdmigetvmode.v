////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmigetvmode.v
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
module	hdmigetvmode(i_clk, i_reset, i_vsync, i_hsync, i_pv,
			o_nlines, o_sstart, o_ssend, o_vtotal);
	input	wire		i_clk, i_reset;
	input	wire		i_vsync, i_hsync, i_pv;
	output	wire	[15:0]	o_nlines;
	output	reg	[15:0]	o_sstart;
	output	reg	[15:0]	o_ssend;
	output	wire	[15:0]	o_vtotal;

	reg	[15:0]	count_lines, count_shelf, count_sync, count_tot;
	reg	last_hs, in_shelf, linestart, has_pixels, has_vsync,
			this_line_had_pixels, last_line_had_pixels, newframe,
			this_line_had_vsync;

	always @(posedge i_clk)
		last_hs <= i_hsync;
	always @(posedge i_clk)
		if ((!last_hs)&&(i_hsync))
		begin
			linestart  <= 1'b1;
			has_pixels <= 1'b0;
			has_vsync  <= 1'b0;
			this_line_had_vsync  <= has_vsync;
			this_line_had_pixels <= has_pixels;
			last_line_had_pixels <= last_line_had_pixels;
			newframe <= (has_pixels)&&(!this_line_had_pixels);
		end else begin
			linestart  <= 1'b0;
			newframe   <= 1'b0;
			if (i_pv)
				has_pixels <= 1'b1;
			if (i_vsync)
				has_vsync  <= 1'b1;
		end


	always @(posedge i_clk)
		if (linestart)
		begin
			if (newframe)
			begin
				count_lines <= 0;
				count_shelf <= 0;
				count_sync  <= 0;
				count_tot   <= 0;
				in_shelf    <= 1'b1;
			end else begin
				if (!(&count_tot))
					count_tot <= count_tot + 1'b1;
				if ((!(&count_lines))&&(this_line_had_pixels))
					count_lines <= count_lines + 1'b1;
				if ((!(&count_sync))&&(this_line_had_vsync))
					count_sync <= count_sync + 1'b1;
				if ((!(&count_shelf))&&(!this_line_had_pixels)
						&&(!this_line_had_vsync)&&(in_shelf))
					count_shelf <= count_shelf + 1'b1;
				if (this_line_had_vsync)
					in_shelf <= 1'b0;
			end
		end

	reg	[15:0]	test_pixcount, test_totcount, test_shelf, test_nsync;
	wire	[15:0]	w_shelf, w_nsync;
	reg		test_valid;
	always @(posedge i_clk)
		if (newframe)
		begin
			test_pixcount <= count_lines + 1'b1;
			test_totcount <= count_tot + 1'b1;
			test_shelf    <= count_shelf;
			test_nsync    <= count_sync;
			test_valid <= 1'b1;
		end else
			test_valid <= 1'b0;

	validatecount vvpix(  i_clk,i_reset,test_valid,test_pixcount, o_nlines);
	validatecount vvtot(  i_clk,i_reset,test_valid,test_totcount, o_vtotal);
	validatecount vvshelf(i_clk,i_reset,test_valid,test_shelf,    w_shelf);
	validatecount vvsync( i_clk,i_reset,test_valid,test_nsync,    w_nsync);


	always @(posedge i_clk)
		o_sstart <= o_nlines + w_shelf;
	always @(posedge i_clk)
		o_ssend  <= o_sstart + w_nsync;

endmodule
