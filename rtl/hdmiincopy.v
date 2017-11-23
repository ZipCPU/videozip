////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmiincopy.v
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
module	hdmiincopy(i_wb_clk, i_pix_clk, i_reset,
		i_pix_eof, i_pix_eol, i_pix_newline,
			i_pix_valid, i_pix_r, i_pix_g, i_pix_b,
		i_wb_en, i_wb_first_address, i_wb_words_per_line,
			i_wb_first_xpos, i_wb_first_ypos,
			i_wb_pix_line, i_wb_nlines,
		i_pix_npix, i_pix_nlines,
		o_wb_cyc, o_wb_stb, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall, i_wb_err);
	parameter	XBITS=13, YBITS=11, FRAMEBITS=(XBITS+YBITS+1),
			AW=24;
	input	wire	i_wb_clk, i_pix_clk, i_reset;
	//
	input	wire	i_pix_eof, i_pix_eol, i_pix_newline,
			i_pix_valid;
	input	wire	[7:0]	i_pix_r, i_pix_g, i_pix_b;
	input	wire	i_wb_en;
	input	wire	[(AW-1):0]	i_wb_first_address;
	input	wire	[(AW-1):0]	i_wb_words_per_line;
	input	wire	[(XBITS-1):0]	i_wb_first_xpos, i_wb_pix_line;
	input	wire	[(YBITS-1):0]	i_wb_first_ypos, i_wb_nlines;
	input	wire	[(XBITS-1):0]	i_pix_npix; // Pixels per h-line
	input	wire	[(YBITS-1):0]	i_pix_nlines;
	//
	//
	output	reg			o_wb_cyc, o_wb_stb;
	output	reg	[(AW-1):0]	o_wb_addr;
	output	reg	[(128-1):0]	o_wb_data;
	input	wire			i_wb_ack, i_wb_stall, i_wb_err;


	reg	[(XBITS-1):0]	pix_raw_line_len, pix_per_line, xloc;
	reg	[(YBITS-1):0]	pix_last_ypos, yloc,
				pix_raw_nlines, pix_nlines;

	reg		long_address_word;
	reg	[1:0]	pixcnt;
	reg		yvalid, xvalid;
	reg	[(AW-1):0]	line_address;

	reg	[(AW-1):0]	pix_words_per_line;
	reg	[(XBITS-1):0]	pix_last_xpos;

	// Horizontal control
	always @(posedge i_pix_clk)
	begin
		if (i_wb_first_xpos < i_pix_npix)
			pix_raw_line_len <= (i_pix_npix - i_wb_first_xpos);
		else
			pix_raw_line_len <= 0;
		if (i_wb_pix_line == 0)
			pix_per_line <= pix_raw_line_len;
		else if (pix_raw_line_len < i_wb_pix_line)
			pix_per_line <= pix_raw_line_len;
		else
			pix_per_line <= i_wb_pix_line;
		pix_last_xpos <= pix_per_line - i_wb_first_xpos;
		//
		if (i_wb_words_per_line == 0)
			pix_words_per_line <= {
				{(AW-(XBITS-2)){1'b0}},pix_per_line[(XBITS-1):2]};
		else
			pix_words_per_line <= i_wb_words_per_line;
	end

	// Synchronized our X position to the incoming data
	always @(posedge i_pix_clk)
		if (i_pix_eol)
		begin
			xloc <= 0;
			xvalid <= (i_wb_first_xpos == 0);
		end else begin
			xvalid <= (xloc + 1'b1 >= i_wb_first_xpos)
				&&(xloc + 1'b1 > pix_last_xpos);
			if (i_pix_valid)
				xloc <= xloc + 1'b1;
		end

	// Vertical control
	always @(posedge i_pix_clk)
	begin
		if (i_wb_first_ypos < i_pix_nlines)
			pix_raw_nlines <= i_wb_first_ypos - i_pix_nlines;
		else
			pix_raw_nlines <= 0;
		if (i_wb_nlines == 0)
			pix_nlines <= pix_raw_nlines;
		else if (i_pix_nlines < i_wb_nlines)
			pix_nlines <= i_pix_nlines;
		else
			pix_nlines <= i_wb_nlines;
		pix_last_ypos <= pix_nlines - i_wb_first_ypos;
	end

	// Synchronized our X position to the incoming data
	always @(posedge i_pix_clk)
		if (i_pix_eof)
			yloc <= 0;
		else if (i_pix_eol)
			yloc <= yloc + 1'b1;
	always @(posedge i_pix_clk)
		yvalid <= (yloc >= i_wb_first_ypos)&&(yloc < pix_last_ypos);

	wire	this_pix_valid = (i_pix_valid)&&(xvalid)&&(yvalid);

	reg	[1:0]	frame_en_pipe;
	reg	[95:0]	long_pixel_word;
	initial	frame_en_pipe = 2'b0;
	always @(posedge i_pix_clk)
		if (i_reset)
			frame_en_pipe <= 2'b0;
		else if (i_pix_eof)
			frame_en_pipe <= { frame_en_pipe[0], i_wb_en };

	wire	frame_en;
	assign	frame_en = frame_en_pipe[1];

	always @(posedge i_pix_clk)
	begin
		if ((i_pix_eof)||(i_reset))
			line_address <= i_wb_first_address;
		else if ((i_pix_newline)&&(i_pix_valid))
			line_address <= line_address + pix_words_per_line;
	end

	//
	//
	// Pack our pixels to the width of the bus, currently four words
	//
	//
	always @(posedge i_pix_clk)
	begin
		if ((this_pix_valid)||(pixcnt != 2'b00))
		begin
			if (this_pix_valid)
				long_pixel_word <= { long_pixel_word[71:0],
					i_pix_r, i_pix_g, i_pix_b };
			else
				long_pixel_word <= { long_pixel_word[71:0],
							24'h00 };
			long_address_word    <= 1'b0;
			pixcnt <= pixcnt + 1'b1;
			write_to_pix_fifo <= (pixcnt == 2'b11)&&(frame_en);
		end else begin
			// 97 - AW
			long_pixel_word <= { {(96-AW){1'b0}}, line_address };
			write_to_pix_fifo <= (!long_address_word)&&(frame_en);
			long_address_word <= 1'b1;
			pixcnt <= 2'b00;
			// pixcnt <= line_address[1:0];
		end

		if (i_reset)
			pixcnt <= 0;
	end

	reg	[2:0]	fifo_lines;
	reg	write_to_pix_fifo;
	wire	read_fifo;
	wire	[96:0]	fifo_data;

	pixfifo	#(.BW(24*4+1)) inpixfifo(i_pix_clk, !frame_en, i_wb_clk,
			(write_to_pix_fifo),
			{ long_address_word, long_pixel_word },
			read_fifo, fifo_data);

	wire	wb_eol_stb;
	transferstb tfreol(i_pix_clk, i_wb_clk, i_pix_eol, wb_eol_stb);

	reg	rd_line_stb;
	initial	rd_line_stb = 1'b0;
	initial	fifo_lines = 3'h00;
	always @(posedge i_wb_clk)
		case({wb_eol_stb, rd_line_stb})
		2'b00: fifo_lines <= fifo_lines;
		2'b01: fifo_lines <= (fifo_lines > 0) ? fifo_lines-1'b1 : 0;
		2'b10: fifo_lines <= (&fifo_lines) ? fifo_lines:fifo_lines+1'b1;
		2'b11: fifo_lines <= fifo_lines;
		endcase

	assign	read_fifo = ((o_wb_stb)&&(!i_wb_ack))
				||((|fifo_lines)&&(fifo_data[96]));
	always @(posedge i_wb_clk)
	begin
		rd_line_stb <= 1'b0;
		if ((!o_wb_cyc)&&(fifo_lines > 0)&&(!fifo_data[96]))
		begin
			o_wb_cyc  <= 1'b1;
			o_wb_stb  <= 1'b1;
			rd_line_stb <= 1'b1;
		end else if ((o_wb_stb)&&(fifo_data[96]))
			o_wb_stb <= 1'b0;
		else if ((r_expected_acks == 1)&&(i_wb_ack))
			o_wb_cyc <= 1'b0;
		else if (r_expected_acks == 0)
			o_wb_cyc <= 1'b0;

		if ((o_wb_stb)&&(!i_wb_stall))
			o_wb_addr <= o_wb_addr + 1'b1;
		else if (fifo_data[96])
			o_wb_addr <= fifo_data[(AW-1):0];

		if ((i_reset)||(i_wb_err))
		begin
			o_wb_cyc <= 1'b0;
			o_wb_stb <= 1'b0;
		end
	end

	reg	[(XBITS-4):0]	r_expected_acks;
	initial	r_expected_acks = 0;
	always @(posedge i_wb_clk)
		if (!o_wb_cyc)
			r_expected_acks <= 0;
		else case({ ((o_wb_stb)&&(!i_wb_stall)), i_wb_ack })
		2'b00: r_expected_acks <= r_expected_acks;
		2'b01: r_expected_acks <= r_expected_acks - 1'b1;
		2'b10: r_expected_acks <= r_expected_acks + 1'b1;
		2'b11: r_expected_acks <= r_expected_acks;
		endcase

	always @(posedge i_wb_clk)
		if (!i_wb_stall)
			o_wb_data <= {  8'h00, fifo_data[95:72],
					8'h00, fifo_data[71:48],
					8'h00, fifo_data[47:24],
					8'h00, fifo_data[23: 0] };
		
endmodule
