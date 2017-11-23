////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmigethmode.v
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
module	hdmigethmode(i_clk, i_reset, i_hsync, i_ispix,
		o_npix, o_sstart, o_ssend, o_htotal);
	parameter	[63:0]	INITIAL_HMODE = 0;
	parameter	[0:0]	INITIAL_GOOD = (INITIAL_HMODE == 0) ? 1'b0:1'b1;
	parameter	[2:0]	INITIAL_COUNT = (INITIAL_GOOD) ? 3'b111:3'b000;
	parameter	[0:0]	KNOWN = (INITIAL_HMODE != 0);
	input	wire		i_clk, i_reset;
	input	wire		i_hsync, i_ispix;
	output	wire	[15:0]	o_npix;
	output	reg	[15:0]	o_sstart;
	output	reg	[15:0]	o_ssend;
	output	wire	[15:0]	o_htotal;

	reg	[15:0]	count_pix, count_shelf, count_sync, count_tot;
	reg	last_pv, in_shelf;

	reg	[15:0]	test_pixcount, test_totcount, test_shelf, test_nsync;
	wire	[15:0]	w_shelf, w_nsync;
	reg		test_valid;

	always @(posedge i_clk)
		last_pv <= i_ispix;

	wire	new_data_row;
	assign	new_data_row = (!last_pv)&&(i_ispix);


	initial	count_pix   = 0;
	initial	count_shelf = 0;
	initial	count_sync  = 0;
	initial	count_tot   = 0;
	initial	in_shelf     = 1'b1;
	always @(posedge i_clk)
		if (new_data_row)
		begin
			count_pix   <= 0;
			count_shelf <= 0;
			count_sync  <= 0;
			count_tot   <= 0;
			in_shelf    <= 1'b1;
		end else begin
			if (!(&count_tot))
				count_tot <= count_tot + 1'b1;
			if ((!(&count_pix))&&(i_ispix))
				count_pix <= count_pix + 1'b1;
			if ((!(&count_sync))&&(i_hsync))
				count_sync <= count_sync + 1'b1;
			if ((!(&count_shelf))&&(!i_ispix)
					&&(!i_hsync)&&(in_shelf))
				count_shelf <= count_shelf + 1'b1;
			if (i_hsync)
				in_shelf <= 1'b0;
		end

	initial	test_pixcount = 0;
	initial	test_totcount = 0;
	initial	test_shelf    = 0;
	initial	test_nsync    = 0;
	initial	test_valid    = 1'b0;
	always @(posedge i_clk)
		if (new_data_row)
		begin
			test_pixcount <= count_pix-16'd10;
			test_totcount <= count_tot+16'd1;
			test_shelf    <= count_shelf + 16'd11;
			test_nsync    <= count_sync;
			test_valid <= (!KNOWN);
		end else
			test_valid <= 1'b0;

	wire	v_reset;
	assign	v_reset = (!KNOWN)&&(i_reset);

	validatecount
		#(.INITIAL_VALUE(INITIAL_HMODE[63:48]),
			.INITIAL_GOOD(INITIAL_GOOD),
			.INITIAL_COUNT(INITIAL_COUNT))
		vpix(  i_clk,v_reset, test_valid, test_pixcount, o_npix);
	validatecount
		#(.INITIAL_VALUE(INITIAL_HMODE[15:0]),
			.INITIAL_GOOD(INITIAL_GOOD),
			.INITIAL_COUNT(INITIAL_COUNT))
		vtot(  i_clk,v_reset, test_valid, test_totcount, o_htotal);
	validatecount
		#(.INITIAL_VALUE(INITIAL_HMODE[47:32]-INITIAL_HMODE[63:48]),
			.INITIAL_GOOD(INITIAL_GOOD),
			.INITIAL_COUNT(INITIAL_COUNT))
		vshelf(i_clk,v_reset, test_valid, test_shelf,    w_shelf);
	validatecount
		#(.INITIAL_VALUE(INITIAL_HMODE[31:16]-INITIAL_HMODE[47:32]),
			.INITIAL_GOOD(INITIAL_GOOD),
			.INITIAL_COUNT(INITIAL_COUNT))
		vsync( i_clk,v_reset, test_valid, test_nsync,    w_nsync);

	initial	o_sstart = INITIAL_HMODE[47:32];
	always @(posedge i_clk)
		o_sstart <= o_npix + w_shelf;
	initial	o_sstart = INITIAL_HMODE[31:16];
	always @(posedge i_clk)
		o_ssend  <= o_sstart + w_nsync;

	// assign	o_dbg = { test_valid, new_data_row, i_ispix, count_tot[6:0], test_totcount[11:0], o_htotal[11:0] };
endmodule
