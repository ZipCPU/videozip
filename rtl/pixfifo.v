////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	pixfifo.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	A very simple FIFO, drawn/borrowed from the WBUART32 project,
//		but herein modified to handle separate read and write clocks.
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
module pixfifo(i_wr_clk, i_pix_reset, i_rd_clk, i_wr, i_data, i_rd, o_data);
	parameter	BW=97;	// Four pixels, plus a pixel v address flag
	parameter [3:0]	LGFLEN=11;	// Enough for 2x lines
	parameter 	RXFIFO=1'b0;	// True if coming from the HDMI decoder
	input	wire		i_wr_clk, i_pix_reset, i_rd_clk;
	input	wire		i_wr;
	input	wire [(BW-1):0]	i_data;
	input	wire		i_rd;
	output	wire [(BW-1):0]	o_data;

	localparam	FLEN=(1<<LGFLEN);

	reg	[(BW-1):0]	fifo[0:(FLEN-1)];
	reg	[(LGFLEN-1):0]	r_wr_first, r_last, r_next;

	wire	[(LGFLEN-1):0]	w_first_plus_one;
	assign	w_first_plus_one = r_wr_first + {{(LGFLEN-1){1'b0}},1'b1};

	reg	[1:0]	wr_reset, rd_reset;
	always @(posedge i_wr_clk, posedge i_pix_reset)
		if (i_pix_reset)
			wr_reset <= 2'b11;
		else
			wr_reset <= { wr_reset[0], 1'b0 };

	always @(posedge i_rd_clk, posedge i_pix_reset)
		if (i_pix_reset)
			rd_reset <= 2'b11;
		else
			rd_reset <= { rd_reset[0], 1'b0 };

	//
	// Write to the FIFO on the write clock, whenever i_wr is true
	// Writes
	initial	r_wr_first = 0;
	always @(posedge i_wr_clk)
		if (wr_reset[1])
			r_wr_first <= 0;
		else if (i_wr)
		begin // Allow/permit overflow, since doing otherwise requires
			// coordination across clocks
			r_wr_first <= w_first_plus_one;
		end
	always @(posedge i_wr_clk)
		// Write our new value regardless--on overflow or not
		fifo[r_wr_first] <= i_data;

	initial	r_last = 0;
	initial	r_next = {{(LGFLEN-2){1'b0}},2'b10};
	always @(posedge i_rd_clk)
		if (rd_reset[1])
		begin
			r_last <= 0;
			r_next <= {{(LGFLEN-2){1'b0}},2'b10};
		end else if (i_rd)
		begin
			r_last <= r_next;
			r_next <= r_last +{{(LGFLEN-2){1'b0}},2'b10};
		end

	reg	last_rd;
	reg	[(BW-1):0]	fifo_here, fifo_next;
	always @(posedge i_rd_clk)
		fifo_here <= fifo[r_last];
	always @(posedge i_rd_clk)
		fifo_next <= fifo[r_next];
	always @(posedge i_rd_clk)
		last_rd <= i_rd;

	reg	osrc;
	always @(posedge i_rd_clk)
		if (last_rd)
			osrc <= 1'b1;
		else
			osrc <= 1'b0;

	assign o_data = (osrc) ? fifo_next:fifo_here;

endmodule
