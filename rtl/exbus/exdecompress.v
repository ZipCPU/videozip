////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exdecompress.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
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
module	exdecompress #(
		// {{{
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk,
					i_reset,
					i_stb,
		output	wire		o_busy,
		input	wire	[34:0]	i_word,
		output	reg		o_stb,
		input	wire		i_busy,
		output	reg	[34:0]	o_word,
		output	wire		o_active
		// }}}
	);

	// Local declarations
	// {{{
	reg	[34:0]	addr_word;
	reg	[34:0]	write_word;
	reg	[9:0]	write_lookup_addr, write_addr;
	reg		write_table_lookup;
	reg	[11:0]	read_count;
	reg		partial_type;
	reg	[31:0]	write_table	[0:(1<<10)-1];

	reg	[1:0]	word_type;
	reg		r_stb, q_stb;
	reg	[4:0]	r_special;
	reg	[34:0]	partial;
	reg	[31:0]	write_table_value;
	reg		write_to_table;

	wire	r_busy, q_busy;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #1:
	//	From:	i_stb, i_word
	//	Create:	r_stb, addr_word, write_word, write_lookup_addr
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Decode the address
	//	Address output is 2'b00, 1'b0, address (if fixed)
	//			2'b00, 1'b1, address offset

	// addr_word
	// {{{
	always @(posedge i_clk)
	if ((!r_stb || !r_busy) && (!OPT_LOWPOWER
			|| (i_stb && !o_busy && i_word[34:33] == 2'b00)))
	casez(i_word[32:29])
	4'b0???:addr_word <= { 3'b000, i_word[31:2], 1'b0, i_word[0] };
	4'b10??:addr_word <= { 3'b001, {(29){i_word[30]}}, i_word[29], 1'b0, i_word[28] };
	4'b1100:addr_word <= { 3'b000, {(24){i_word[28]}}, i_word[27:22], 1'b0, i_word[21] };
	4'b1101:addr_word <= { 3'b001, {(24){i_word[28]}}, i_word[27:22], 1'b0, i_word[21] };
	4'b1110:addr_word <= { 3'b000, {(17){i_word[28]}}, i_word[27:15], 1'b0, i_word[14] };
	4'b1111:addr_word <= { 3'b001, {(17){i_word[28]}}, i_word[27:15], 1'b0, i_word[14] };
	endcase
`ifdef	FORMAL
	always @(*)
	if (r_stb)
		assert(addr_word[34:33] == 2'b00);
`endif
	// }}}

	// write_word: Decode the write word
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	casez(i_word[32:30])
	3'b0??:write_word <= { 3'b010, i_word[31:0] };
	3'b1?0:write_word <= { 3'b010, {(24){i_word[29]}}, i_word[28:21] };
	3'b1?1:write_word <= { 3'b010, {(17){i_word[29]}}, i_word[28:14] };
	endcase
	// }}}

	// write_lookup_addr
	// {{{
	always @(posedge i_clk)
	if (i_stb && !o_busy)
	begin
		if (OPT_LOWPOWER && i_word[34:33] != 2'b01)
			write_lookup_addr <= 0;
		else case(i_word[30])
		1'b0:write_lookup_addr<= { 8'hff, ~i_word[29:28] } + write_addr + (write_to_table ? 1:0);
		1'b1:write_lookup_addr<= { 1'b1,  ~i_word[29:21] } + write_addr + (write_to_table ? 1:0);
		endcase
	end
	// }}}

	// write_table_lookup
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		write_table_lookup <= 1'b0;
	else if (i_stb && !o_busy)
	begin
		if (OPT_LOWPOWER)
			write_table_lookup <= (i_word[34:31] == 4'b0110);
		else
			write_table_lookup <= (i_word[32:31] == 2'b10);
	end else if (!r_busy)
		write_table_lookup <= 1'b0;
	// }}}

	// read_count
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		read_count <= 0;
	else if (i_stb && !o_busy)
	case(i_word[32])
	1'b0: read_count <= 12'd1  + { 8'h0, i_word[31:28] }; // 1-16
	1'b1: read_count <= 12'd17 + { 1'b0, i_word[31:21] };	// 17-2064
	endcase
	// }}}

	// word_type
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		word_type <= 2'b00;
	else if (i_stb && !o_busy)
		word_type <= i_word[34:33];
	// }}}

	// r_stb, r_special, write_to_table
	// {{{
	initial	r_stb = 1'b0;
	initial	write_to_table = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_stb <= 1'b0;
		write_to_table <= 1'b0;
	end else if (i_stb && !o_busy)
	begin
		r_stb <= 1'b1;
		write_to_table <= i_word[34:33] == 2'b01
			&& (!i_word[32] || i_word[32:30] == 3'b111);
	end else if (!r_busy)
		{ write_to_table, r_stb } <= 2'b0;

	always @(posedge i_clk)
	if (i_stb && !o_busy)
		r_special <= i_word[32:28];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #2:
	//	Create: q_stb, partial, partial_type, write_table,
	//		write_table_value
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// q_stb
	// {{{
	initial	q_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		q_stb <= 1'b0;
	else if (r_stb && !r_busy)
		q_stb <= 1'b1;
	else if (!q_busy)
		q_stb <= 1'b0;
	// }}}

	// partial
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		partial <= 35'h0;
	else if (r_stb && !r_busy)
	case(word_type)
	2'b00: partial <=  addr_word;
	2'b01: partial <= write_word;
	2'b10: partial <= { 2'b10, {(21){1'b0}}, read_count };
	2'b11: partial <= { 2'b11, r_special, 28'h0 };
	endcase
	// }}}

	// partial_type
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		partial_type <= 1'b0;
	else if (r_stb && !r_busy)
		partial_type <= write_table_lookup && word_type == 2'b01;
	// }}}

	// Write to our compression table
	// {{{
	always @(posedge i_clk)
	if (write_to_table && !r_busy)
		write_table[write_addr] <= write_word[31:0];
	// }}}

	// write_addr
	// {{{
	initial	write_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		write_addr <= 0;
	else if (write_to_table && !r_busy)
		write_addr <= write_addr + 1;
	// }}}

	// write_table_value
	// {{{
	always @(posedge i_clk)
	if (write_table_lookup && !r_busy)
		write_table_value <= write_table[write_lookup_addr];
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock #3:
	//	Create: o_stb, o_word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	// o_stb
	// {{{
	initial	o_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_stb <= 1'b0;
	else if (q_stb && !q_busy)
		o_stb <= 1'b1;
	else if (!i_busy)
		o_stb <= 1'b0;
	// }}}

	// o_word
	// {{{
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		o_word <= 0;
	else if (!q_busy)
	begin
		if (q_stb && partial_type)
			o_word <= { 3'b010, write_table_value };
		else
			o_word <= partial;
	end
	// }}}

	assign	q_busy = o_stb && i_busy;
	assign	r_busy = q_stb && q_busy;
	assign	o_busy = r_stb && r_busy;
	assign	o_active = r_stb || q_stb;
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
	reg	f_past_valid;
	reg		fq_valid, fr_valid, fo_valid;
	reg	[34:0]	fq_word, fr_word, fo_word;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Stream properties
	// {{{

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_stb);
	else if ($past(i_stb && o_busy))
		assume(i_stb && $stable(i_word));

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_stb);
	else if ($past(o_stb && i_busy))
		assert(o_stb && $stable(o_word));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Induction
	// {{{

	// R-Stage
	// {{{
	initial	fr_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		fr_valid <= 1'b0;
	else if (i_stb && !o_busy)
		fr_valid <= 1'b1;
	else if (!fq_valid || !o_stb || !i_busy)
		fr_valid <= 1'b0;

	always @(posedge i_clk)
	if (i_stb && !o_busy)
		fr_word <= i_word;

	always @(*)
	begin
		assert(r_stb == fr_valid);
		assert(!f_past_valid || !fr_valid
					|| fr_word[34:33] == word_type);
		if(f_past_valid && fr_valid)
		begin
			if (fr_word[32:31] != 2'b10)
			begin
				assert(!write_table_lookup);
			end else if (OPT_LOWPOWER)
			begin
				assert(write_table_lookup == (fr_word[34:31] == 4'h6));
			end else
				assert(write_table_lookup);

			if(fr_word[34:33] == 2'b10)
			case(fr_word[32])
			1'b0: assert(read_count == 12'd1  + { 8'h0, fr_word[31:28] });
			1'b1: assert(read_count == 12'd17 + { 1'b0, fr_word[31:21] });
			endcase
		end
	end

	always @(*)
	if (fr_valid)
	case(fr_word[34:33])
	2'b00: begin
		assert(word_type == 2'b00);
		casez(fr_word[32:30])
		3'b0??: assert(addr_word == { 3'h0, fr_word[31:2], 1'b0, fr_word[0] });
		3'b10?: assert(addr_word == { 3'b001, {(29){fr_word[30]}}, fr_word[29], 1'b0, fr_word[28] });
		3'b110: assert(addr_word == { 2'b00, fr_word[29], {(24){fr_word[28]}}, fr_word[27:22], 1'b0, fr_word[21] });
		3'b111: assert(addr_word == { 2'b00, fr_word[29], {(17){fr_word[28]}}, fr_word[27:15], 1'b0, fr_word[14] });
		default: begin end
		endcase end
	2'b01: begin // Write
		casez(fr_word[32:30])
		3'b0??: assert(write_word == fr_word);
		3'b110: assert(write_word == {3'b010, {(24){fr_word[29]}}, fr_word[28:21]});
		3'b111: assert(write_word == { 3'b010, {(17){fr_word[29]}}, fr_word[28:14]});
		default: assert(write_word[34:32] == 3'b010);
		endcase end
	// 2'b01: begin end
	2'b11: assert(r_special == fr_word[32:28]);
	default: begin end
	endcase
	// }}}

	// Q-Stage
	// {{{
	initial	fq_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		fq_valid <= 1'b0;
	else if (fr_valid && (!fq_valid || !o_stb || !i_busy))
		fq_valid <= 1'b1;
	else if (!o_stb || !i_busy)
		fq_valid <= 1'b0;

	always @(posedge i_clk)
	if (fr_valid && (!fq_valid || !o_stb || !i_busy))
		fq_word <= fr_word;

	always @(*)
	begin
		assert(q_stb == fq_valid);
	end

	always @(*)
	if (f_past_valid && fq_valid)
	begin
		assert(partial[34:33] == fq_word[34:33]);
		assert(partial_type == (fq_word[34:31] == 4'b0110));
	end

	always @(*)
	if (fq_valid)
	case(fq_word[34:33])
	2'b00: begin
		casez(fq_word[32:30])
		3'b0??: assert(partial == { 3'h0, fq_word[31:2], 1'b0, fq_word[0] });
		3'b10?: assert(partial == { 3'b001, {(29){fq_word[30]}}, fq_word[29], 1'b0, fq_word[28] });
		3'b110: assert(partial == { 2'b00, fq_word[29], {(24){fq_word[28]}}, fq_word[27:22], 1'b0, fq_word[21] });
		3'b111: assert(partial == { 2'b00, fq_word[29], {(17){fq_word[28]}}, fq_word[27:15], 1'b0, fq_word[14] });
		default: begin end
		endcase end
	2'b01: begin
		casez(fq_word[32:30])
		3'b0??: assert(partial == fq_word);
		3'b110: assert(partial == { 3'b010, {(24){fq_word[29]}}, fq_word[28:21]});
		3'b111: assert(partial == { 3'b010, {(17){fq_word[29]}}, fq_word[28:14]});
		default: begin end
		endcase end
	2'b10: begin
		casez(fq_word[32])
		1'b0: assert(partial == { 3'b100, 28'h0, fq_word[31:28]}+ 35'd1);
		// 500E30018
		// 101,000_0000,011_1000,11
		1'b1: assert(partial == { 3'b100, 21'h0, fq_word[31:21]}+35'd17);
		endcase end
	2'b11: assert(partial[32:28] == fq_word[32:28]);
	endcase
	// }}}

	// O/Output-Stage
	// {{{
	initial	fo_valid = 0;
	always @(posedge i_clk)
	if (i_reset)
		fo_valid <= 1'b0;
	else if (!o_stb || !i_busy)
		fo_valid <= fq_valid;

	always @(posedge i_clk)
	if (!o_stb || !i_busy)
		fo_word <= fq_word;

	always @(*)
		assert(o_stb == fo_valid);

	always @(*)
	if (fo_valid)
	case(fo_word[34:33])
	2'b00: begin
		casez(fo_word[32:30])
		3'b0??: assert(o_word == { 3'h0, fo_word[31:2], 1'b0, fo_word[0] });
		3'b10?: assert(o_word == { 3'b001, {(29){fo_word[30]}}, fo_word[29], 1'b0, fo_word[28] });
		3'b110: assert(o_word == { 2'b00, fo_word[29], {(24){fo_word[28]}}, fo_word[27:22], 1'b0, fo_word[21] });
		3'b111: assert(o_word == { 2'b00, fo_word[29], {(17){fo_word[28]}}, fo_word[27:15], 1'b0, fo_word[14] });
		default: begin end
		endcase end
	2'b01: begin
		casez(fo_word[32:30])
		3'b0??: assert(o_word == fo_word);
		3'b110: assert(o_word == {3'b010, {(24){fo_word[29]}}, fo_word[28:21]});
		3'b111: assert(o_word == { 3'b010, {(17){fo_word[29]}}, fo_word[28:14]});
		default: begin end
		endcase end
	2'b10: begin
		casez(fo_word[32])
		1'b0: assert(o_word == { 3'b100, 28'h0, fo_word[31:28]}+ 35'd1);
		// 500E30018
		// 101,000_0000,011_1000,11
		1'b1: assert(o_word == { 3'b100, 21'h0, fo_word[31:21]}+35'd17);
		endcase end
	2'b11: assert(o_word[32:28] == fo_word[32:28]);
	endcase
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract properties
	// {{{

// TODO/FIXME: Need to formally verify the table lookup still

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// o_active properties
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_active);
	else if ($past(i_stb && !o_busy))
		assert(o_active);
	else if ($past(o_active))
		assert(o_active || o_stb);
	else
		assert(!$rose(o_stb));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// cover properties
	// {{{

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && o_stb)
	case(o_word[34:33])
	2'b00: begin
		cover(!fo_word[32]);
		cover( fo_word[32:31] == 2'b10);
		cover( fo_word[32:30] == 3'b110);
		cover( fo_word[32:30] == 3'b111);
		end
	2'b01: begin
		cover(!fo_word[32]);
		cover( fo_word[32:30] == 3'b100);
		cover( fo_word[32:30] == 3'b101);
		cover( fo_word[32:30] == 3'b110);
		cover( fo_word[32:30] == 3'b111);
		end
	2'b10: begin
		cover(!fo_word[32]);
		cover( fo_word[32]);
		end
	2'b11: cover(1);
	endcase
	// }}}
`endif
// }}}
endmodule

