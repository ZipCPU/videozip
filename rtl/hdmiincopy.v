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
module	hdmiincopy(i_wb_clk, i_pix_clk, i_reset,
		i_pix_eof, i_pix_eol, i_pix_newframe, i_pix_newline,
			i_pix_valid, i_pix_r, i_pix_g, i_pix_b,
		i_wb_en, i_wb_first_address, i_wb_bytes_per_line,
			i_wb_first_xpos, i_wb_first_ypos,
			i_wb_pix_line, i_wb_nlines,
		i_pix_npix, i_pix_nlines,
		o_wb_cyc, o_wb_stb, o_wb_addr, o_wb_data,
			i_wb_ack, i_wb_stall);


	// Horizontal control
	always @(posedge i_pix_clk)
	begin
		if (i_wb_first_xpos < i_pix_npix)j
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
		if (i_wb_words_per_line == 0)
			pix_words_per_line <= pix_per_line;
		else
			pix_words_per_line <= i_wb_words_per_line;
	end

	// Synchronized our X position to the incoming data
	always @(posedge i_clk)
		if (i_pix_eol)
		begin
			xloc <= 0;
			xvalid <= (i_wb_first_xpos == 0);
		else begin
			xvalid <= (xpos + 1'b1 >= i_wb_first_xpos)
				&&(xpos + 1'b1 > pix_last_xpos);
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
	always @(posedge i_clk)
		if (i_pix_eof)
			yloc <= 0;
		else if (i_pix_eol)
			yloc <= yloc + 1'b1;
	always @(posedge i_clk)
		yvalid <= (yloc >= i_wb_first_ypos)&&(yloc < pix_last_ypos);


	// Create a new pix-valid, based upon the desired start and stop on
	// the line
	always @(posedge i_pix_clk)
		r_pix_valid <= (i_pix_valid)&&(xvalid)&&(yvalid);
	always @(posedge i_pix_clk)
	begin
		if (i_pix_eof)
		begin
			base_address <= i_wb_first_address;
			line_address <= i_wb_first_address;
		end else if ((i_pix_newline)&&(i_pix_valid))
			line_address <= line_address + pix_words_per_line;

		if ((i_pix_valid)&&(xvalid)&&(yvalid))
			pixel <= { 1'b0, 6'h0, i_pix_r, i_pix_g, i_pix_b };
		else
			pixel <= { 1'b1, line_address };
		fifo_write <= ((i_pix_valid)&&(xvalid)&&(yvalid))
			||(last_pix_valid);
		last_pix_valid <= (i_pix_valid)&&(xvalid)&&(yvalid);
	end

	// Pack our pixels to the width of the bus, currently four words
	reg		long_address_word;
	reg	[1:0]	pixcnt;
	reg	[3:0]	long_pixel_phase;
	wire	this_pix_valid = (i_pix_valid)&&(xvalid)&&(yvalid);
	always @(posedge i_pix_clk)
		if ((this_pix_valid)||(pxcnt != 2'b00))
		begin
			if (this_pix_valid)
				long_pixel_word <= { long_pixel_word[71:0],
					i_pix_r, i_pix_g, i_pix_b };
			else
				long_pixel_word <= { long_pixel_word[71:0],
							24'h00 };
			long_address_word    <= 1'b0;
			pixcnt <= pixcnt + 1'b1;
			write_to_pix_fifo <= (pixcnt == 2'b11);
		end else begin
			long_pixel_word <= { 72'h00, line_address };
			write_to_pix_fifo <= (!long_address_word);
			long_address_word <= 1'b1;
			pixcnt <= 2'b00;
		end

	pixfifo	inpixfifo(i_pix_clk, i_wb_clk,
			(write_to_pix_fifo),
			{ long_address_word, long_pixel_word },
			read_fifo, fifo_data);

	transferstb tfreol(i_pix_clk, i_wb_clk, i_eol, wb_eol_stb);

	initial	fifo_lines = 3'h00;
	always @(posedge i_wb_clk)
		case({wb_eol_stb, rd_line_stb})
		2'b00: fifo_lines <= fifo_lines;
		2'b01: fifo_lines <= (fifo_lines > 0) ? fifo_lines-1'b1 : 0;
		2'b10: fifo_lines <= (&fifo_lines) ? fifo_lines:fifo_lines+1'b1;
		2'b11: fifo_lines <= fifo_lines;
		endcase

	assign	read_fifo = ((o_wb_stb)&&(!i_wb_ack))
				||((|fifo_lines)&&(fifo_data[96]))
	always @(posedge i_wb_clk)
	begin
		if ((!o_wb_cyc)&&(fifo_lines > 0)&&(!fifo_data[96]))
		begin
			o_wb_cyc  <= 1'b1;
			o_wb_stb  <= 1'b1;
		end else if ((o_wb_stb)&&(fifo_data[96]))
			o_wb_stb <= 1'b0;
		end else if ((r_expected_acks == 1)&&(i_wb_ack))
			o_wb_cyc <= 1'b0;
		end else if (r_expected_acks == 0)
			o_wb_cyc <= 1'b0;

		if ((o_wb_stb)&&(!i_wb_stall))
			o_wb_addr <= o_wb_addr + 1'b1;
		else if (fifo_data[96])
			o_wb_addr <= { fifo_data[29:0], 2'b00 };
	end

	always @(posedge i_wb_clk)
		if (!o_wb_cyc)
			r_expected_acks <= 1'b0;
		else case({ ((o_wb_stb)&&(!i_wb_stall)), i_wb_ack })
		2'b00: r_expected_acks <= r_expected_acks;
		2'b10: r_expected_acks <= r_expected_acks - 1'b1;
		2'b10: r_expected_acks <= r_expected_acks + 1'b1;
		2'b11: r_expected_acks <= r_expected_acks;
		endcase

	always @(posedge i_wb_clk)
		if (!i_wb_stall)
			o_wb_data <= {  8'h00, fifo_data[95:72],
					8'h00, fifo_data[71:48]
					8'h00, fifo_data[47:24]
					8'h00, fifo_data[23: 0] };
		
endmodule
