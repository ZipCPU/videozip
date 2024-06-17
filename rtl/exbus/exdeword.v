////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exdeword.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Once a word has come from the bus, undergone compression, had
//		idle cycles and interrupts placed in it, this routine converts
//	that word form a 35-bit single word into a series of 7-bit bytes
//	that can head to the output routine.  Hence, it 'deword's the value:
//	unencoding the 35-bit word encoding.
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
`default_nettype none
// }}}
module	exdeword (
		// {{{
		input	wire		i_clk, i_reset,
		// GPIO bits
		// input	wire	[1:0]	i_gpio, -- in exidle, not here
		// The incoming 35-bit codeword
		// {{{
		input	wire		i_stb,
		output	wire		o_busy,
		input	wire	[34:0]	i_word,
		input	wire		i_last,
		// }}}
		// The outgoing 7-bit channel
		// {{{
		output	reg		o_stb,
		input	wire		i_busy,
		output	reg	[6:0]	o_byte,
		output	reg		o_last
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg		r_last;
	reg	[2:0]	w_len;
	reg	[2:0]	r_len;
	reg	[27:0]	r_word;
	// }}}

	// w_len
	// {{{
	// This is where any specific special sauce is located
	always @(*)
	casez(i_word[34:30])
	// Address words
	5'b000??: w_len = 3'h4;	// Long address
	5'b0010?: w_len = 3'h0; //  3-bit signed displacement
	5'b00110: w_len = 3'h1; // 10-bit offset
	5'b00111: w_len = 3'h2; // 14-bit offset
	// Write acks
	5'b10???: w_len = 3'h0;	// Number of acknowledgments
	// Read responses
	5'b010??: w_len = 3'h4;	// Long word response
	5'b01100: w_len = 3'h0;	//  2-bit repeat
	5'b01101: w_len = 3'h1; //  9-bit repeat offset
	5'b01110: w_len = 3'h1; //  9-bit signed number
	5'b01111: w_len = 3'h2; // 16-bit signed value
	// Specials
	5'b11???: w_len = 3'h0;	// Single byte pass through
	endcase
	// }}}

	// r_word, o_byte, o_last
	// {{{
	// A basic shift register, shifting out the top w_len (then r_len) bytes
	initial	o_byte = 7'h0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_word <= 28'h0;
		o_byte <= 7'h0;
		o_last <= 1'b0;
		r_last <= 1'b0;
	end else if (i_stb && !o_busy) // Only accept when not busy
	begin
		r_word <= i_word[27:0];
		o_byte <= i_word[34:28];	// Type 7 bits, always
		o_last <= (w_len == 0) && i_last;
		r_last <= (w_len != 0) && i_last;
	end else if (!i_busy && (r_len != 0))
	begin
		// Shift the rest of the bits out
		o_byte <= r_word[27:21];
		r_word <= { r_word[20:0], 7'h0 };
		o_last <= (r_len <= 1) && r_last;
	end
	// }}}

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (o_stb && r_len == 0 && !i_busy)
		o_stb <= 1'b0;
	else if (i_stb)
		o_stb <= 1'b1;
	// }}}

	// r_len
	// {{{
	initial	r_len = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_len <= 0;
	else if (i_stb && !o_busy)
		r_len <= w_len;
	else if (!i_busy && (r_len > 0))
		r_len <= r_len - 1;
	// }}}

	// o_busy
	// {{{
	assign	o_busy = o_stb;
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg		f_past_valid;
	reg	[34:0]	fvword;
	reg	[4:0]	five_seq;
	reg	[3:0]	four_seq;
	reg	[2:0]	three_seq;
	reg	[1:0]	two_seq;
	reg		one_seq;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(posedge i_clk)
	if (f_past_valid && $past(i_stb && !i_reset && o_busy))
	begin
		assume(i_stb);
		assume($stable(i_word));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);
	else if ($past(o_stb && !i_reset && i_busy))
	begin
		assert(o_stb);
		assert($stable(o_byte));
	end

	always @(*)
		assert(o_busy == o_stb);

	always @(posedge i_clk)
	if (!o_busy)
		fvword <= i_word;

	initial	five_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		five_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b100)
		five_seq <= 1;
	else if (!i_busy)
		five_seq <= five_seq << 1;

	always @(*)
	case(five_seq)
	0: begin end // This is the idle state, no assertions required
	5'b0_0001: begin
		assert(o_stb);
		assert(o_byte == fvword[34:28]);
		assert(r_len == 3'b100);
		assert(r_word == fvword[27:0]);
		assert(o_busy);
		end
	5'b0_0010: begin
		assert(o_stb);
		assert(o_byte == fvword[27:21]);
		assert(r_len == 3'b011);
		assert(r_word[27:7] == fvword[20:0]);
		assert(o_busy);
		end
	5'b0_0100: begin
		assert(o_stb);
		assert(o_byte == fvword[20:14]);
		assert(r_len == 3'b010);
		assert(r_word[27:14] == fvword[13:0]);
		assert(o_busy);
		end
	5'b0_1000: begin
		assert(o_stb);
		assert(o_byte == fvword[13:7]);
		assert(r_len == 3'b001);
		assert(r_word[27:21] == fvword[6:0]);
		assert(o_busy);
		end
	5'b1_0000: begin
		assert(o_stb);
		assert(o_byte == fvword[6:0]);
		assert(r_len == 3'b000);
		assert(o_busy);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	four_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		four_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b011)
		four_seq <= 1;
	else if (!i_busy)
		four_seq <= four_seq << 1;

	always @(*)
	case(four_seq)
	0: begin end // This is the idle state, no assertions required
	4'b0001: begin
		assert(o_byte == fvword[34:28]);
		assert(r_len == 3'b011);
		assert(r_word == fvword[27:0]);
		assert(o_busy && o_stb);
		end
	4'b0010: begin
		assert(o_byte == fvword[27:21]);
		assert(r_len == 3'b010);
		assert(r_word[27:7] == fvword[20:0]);
		assert(o_busy && o_stb);
		end
	4'b0100: begin
		assert(o_byte == fvword[20:14]);
		assert(r_len == 3'b001);
		assert(r_word[27:14] == fvword[13:0]);
		assert(o_busy && o_stb);
		end
	4'b1000: begin
		assert(o_byte == fvword[13:7]);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	three_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		three_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b010)
		three_seq <= 1;
	else if (!i_busy)
		three_seq <= three_seq << 1;

	always @(*)
	case(three_seq)
	0: begin end // This is the idle state, no assertions required
	3'b001: begin
		assert(o_byte == fvword[34:28]);
		assert(r_len == 3'b010);
		assert(r_word == fvword[27:0]);
		assert(o_busy && o_stb);
		end
	3'b010: begin
		assert(o_byte == fvword[27:21]);
		assert(r_len == 3'b001);
		assert(r_word[27:7] == fvword[20:0]);
		assert(o_busy && o_stb);
		end
	3'b100: begin
		assert(o_byte == fvword[20:14]);
		assert(r_len == 3'b000);
		assert(r_word[27:14] == fvword[13:0]);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase

	////////////////////////////////////////////////////////////////////////

	initial	two_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		two_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b001)
		two_seq <= 1;
	else if (!i_busy)
		two_seq <= two_seq << 1;

	always @(*)
	case(two_seq)
	0: begin end // This is the idle state, no assertions required
	2'b001: begin
		assert(o_byte == fvword[34:28]);
		assert(r_len == 3'b001);
		assert(r_word == fvword[27:0]);
		assert(o_busy && o_stb);
		end
	2'b10: begin
		assert(o_byte == fvword[27:21]);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
		end
	default: assert(0);
	endcase


	////////////////////////////////////////////////////////////////////////

	initial	one_seq = 0;
	always @(posedge i_clk)
	if (i_reset)
		one_seq <= 0;
	else if (i_stb && !o_busy && w_len == 3'b000)
		one_seq <= 1;
	else if (!i_busy)
		one_seq <= one_seq << 1;

	always @(*)
	if(one_seq)
	begin
		assert(o_byte == fvword[34:28]);
		assert(r_len == 3'b000);
		assert(o_busy && o_stb);
	end

	////////////////////////////////////////////////////////////////////////
	always @(*)
	assert(o_busy ==(|{ five_seq, four_seq, three_seq, two_seq, one_seq }));

	always @(*)
	if (five_seq)
		assert({ four_seq, three_seq, two_seq, one_seq } == 0);
	else if (four_seq)
		assert({ three_seq, two_seq, one_seq } == 0);
	else if (three_seq)
		assert({ two_seq, one_seq } == 0);
	else if (two_seq)
		assert({ one_seq } == 0);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(!i_busy))
	begin
		cover($past(|five_seq)  && five_seq  == 0);
		// cover($past(|four_seq)  && four_seq  == 0); Never happen
		cover($past(|three_seq) && three_seq == 0);
		cover($past(|two_seq)   && two_seq   == 0);
		cover($past(|one_seq)   && one_seq   == 0);
	end

	always @(*)
	begin
		// We have no four byte sequences
		assert(four_seq == 0);
	end
`endif
// }}}
endmodule

