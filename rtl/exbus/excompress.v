////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/excompress.v
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
module	excompress #(
		parameter [0:0]	OPT_LOWPOWER = 1'b0
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// Incoming data stream
		// {{{
		input	wire		i_stb,
		input	wire	[34:0]	i_word,
		output	wire		o_busy,
		// }}}
		// Outgoing data stream
		// {{{
		output	reg		o_stb,
		output	reg	[34:0]	o_word,
		input	wire		i_busy,
		// }}}
		// o_active : do we have something in our pipeline, not o_stb?
		output	wire		o_active
		// }}}
	);

	// Local registers
	// {{{
	reg		ack_stb, ack_full;
	reg	[34:0]	ack_word;
	wire		ack_increment;
	reg	[31:0]	diff_addr, ack_addr;

	reg		a_stb;
	wire		a_busy;
	reg	[34:0]	a_word;

	reg	[3:0]	rd_amatch;
	reg	[127:0]	match;
	reg		rd_small, rd_bigger;
	reg	[4:0]	w_match;
	reg	[3:0]	matchv;

	wire		r_busy;
	reg		r_stb, r_matched;
	reg	[31:0]	r_value;
	reg	[34:0]	r_word;

	reg	[8:0]	tbl_base, tbl_rdindex;
	reg	[9:0]	tbl_read_index;
	reg		tbl_full, tbl_valid, table_match;
	wire		tbl_reading;
	reg	[31:0]	tbl_mem		[0:511];
	reg	[31:0]	tbl_rdvalue;
	reg	[13:0]	tbl_word;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// First stage: accumulate write acks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// ack_word
	initial	ack_stb  = 1'b0;
	initial	ack_full = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ack_stb <= 1'b0;
		ack_word <= i_word;
		ack_full<= 0;
	end else if (!ack_stb || !a_busy)
	begin
		ack_stb <= i_stb;
		ack_word <= i_word;
		ack_full<= 0;
	end else if (ack_increment)
	begin
		ack_word[32:28] <= ack_word[32:28] + 1;
		ack_full <= (&ack_word[32:29]);
	end

	assign	ack_increment = (i_stb && ack_word[34:33] == 2'b10
				&& i_word[34:33] == 2'b10 && !ack_full);
	assign	o_busy = (ack_stb && a_busy) && (!ack_increment);
`ifdef	FORMAL
	always @(*)
		assert(ack_full == (ack_stb && ack_word[34:28] == 7'b10_11111));
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!ack_stb);
`endif

	// ack_addr -- what address are we acknowledging data for
	// {{{
	// This will be used with diff_addr to return differential addresses
	initial	ack_addr = 0;
	always @(posedge i_clk)
	if (i_reset)
		ack_addr <= 0;
	else if (i_stb && !o_busy)
	begin
		case(i_word[34:33])
		2'b00: ack_addr <= i_word[31:0];
		2'b01: if (ack_addr[0])
			ack_addr <= ack_addr + 4;
		2'b10: if (ack_addr[0])
			ack_addr <= ack_addr + 4;
		2'b11: begin end
		endcase
	end
	// }}}

	// diff_adr -- when using difference addressing, what's the difference?
	// {{{
	initial	diff_addr = 0;
	always @(posedge i_clk)
	if (OPT_LOWPOWER && i_reset)
		diff_addr <= 0;
	else if (i_stb && !o_busy)
	begin
		diff_addr <= 0;
		if (!OPT_LOWPOWER || i_word[34:33] == 2'b00)
			diff_addr[31:2] <= i_word[31:2] - ack_addr[31:2];
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Stage #2: a_*, and rd_*
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	a_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		a_stb <= 1'b0;
	else if (!a_busy)
		a_stb <= ack_stb;

	wire	ack_z8, ack_z11, ack_z15, ack_z16;
	wire	ack_n8, ack_n11, ack_n15, ack_n16;

	assign	ack_z16 = (ack_word[31:16] == 0);
	assign	ack_n16 = (&ack_word[31:16]);

	assign	ack_z15 = (ack_word[31:15] == 0);
	assign	ack_n15 = (&ack_word[31:15]);

	assign	ack_z11 = (ack_word[31:11] == 0);
	assign	ack_n11 = (&ack_word[31:11]);

	assign	ack_z8 = (ack_word[31:8] == 0);
	assign	ack_n8 = (&ack_word[31:8]);

	// a_word: The (compressed) address word
	// {{{
	always @(posedge i_clk)
	if ((!OPT_LOWPOWER || ack_stb) && (!a_stb || !a_busy))
	begin
		a_word <= ack_word;
		if (ack_word[34:33] == 2'b00)
		begin
			// In order of priority from worst to best

			// 15-bit address: 00 1 11
			if ((&diff_addr[31:16])||(diff_addr[31:16] == 0))
				// Differential
				a_word[34:14] <= { 6'b001111, diff_addr[16:2] };
			if (ack_n16 || ack_z16)
				// Signed 14'bit
				a_word[34:14] <= { 6'b001110, ack_word[16:2] };

			// 8'bit address: 00 1 10
			if ((&diff_addr[31:11])||(diff_addr[31:11] == 0))
				// Differential
				a_word[34:21] <= { 6'b001101, diff_addr[9:2] };
			if (ack_n11 || ack_z11)
				// Signed 10'bit
				a_word[34:21] <= { 6'b001100, ack_word[9:2] };

			// 3'bit difference
			if ((&diff_addr[31:4])||(diff_addr[31:4] == 0))
				a_word[34:28] <= { 4'b0010, diff_addr[4:2] };
		end
	end
	// }}}

	assign	a_busy = a_stb && r_busy;

	// Last read data shift register

	// rd_small, rd_bigger
	// {{{
	initial { match, rd_small, rd_bigger } = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		rd_small <= 0;
		rd_bigger <= 0;
	end else if (!a_busy && ack_stb)
	begin
		// Load a new word in
		rd_small  <= ack_z8  || ack_n8;
		rd_bigger <= ack_z15 || ack_n15;

		if (ack_word[34:33] != 2'b01)
		begin
			rd_small  <= 0;
			rd_bigger <= 0;
		end
	end else if (!r_busy)
	begin
		rd_small  <= 0;
		rd_bigger <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (!a_stb || a_word[34:33] != 2'b01)
	begin
		assert(rd_small == 0);
		assert(rd_bigger == 0);
	end
`endif
	// }}}

	// rd_amatch
	// {{{
	always @(*)
	begin
		w_match[0] = matchv[0] && ack_word[31:0] == a_word[ 31: 0];
		w_match[1] = matchv[0] && ack_word[31:0] == match[ 31: 0];
		w_match[2] = matchv[1] && ack_word[31:0] == match[ 63:32];
		w_match[3] = matchv[2] && ack_word[31:0] == match[ 95:64];
		w_match[4] = matchv[3] && ack_word[31:0] == match[127:96];

		if (ack_word[34:33] != 2'b01)
			w_match = 0;
	end

	initial	rd_amatch = 0;
	always @(posedge i_clk)
	if (i_reset)
		rd_amatch <= 0;
	else if (ack_stb && !a_busy)
	begin
		rd_amatch <= 0;
		if (a_stb && a_word[34:33] == 2'b01 && rd_amatch == 0)
		begin
			// New value in the a_* pipeline stage, a value that
			// hasn't been written to the table yet
			rd_amatch[3:0] <= w_match[3:0];
		end else begin
			rd_amatch[3:0] <= w_match[4:1];
		end

		if (ack_word[34:33] != 2'b01
					|| (a_stb && a_word[34:33] == 2'b00))
			rd_amatch <= 0;
	end
`ifdef	FORMAL
	always @(*)
	if (rd_amatch != 0 && a_stb && a_word[34:33] == 2'b01)
	begin
		if (rd_amatch[0])
			assert(a_word[31:0] == match[ 31: 0] && matchv[0]);
		if (rd_amatch[1])
			assert(a_word[31:0] == match[ 63:32] && matchv[1]);
		if (rd_amatch[2])
			assert(a_word[31:0] == match[ 95:64] && matchv[2]);
		if (rd_amatch[3])
			assert(a_word[31:0] == match[127:96] && matchv[3]);
	end
`endif
	// }}}

	// match
	// {{{
	initial	match  = 0;
	initial	matchv = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		match <= 0;
		matchv <= 0;
	end else if (a_stb && !a_busy)
	begin
		if (a_word[34:33] == 2'b00)
			// Clear any potential matches following a new address
			matchv <= 0;
		else if(a_word[34:33] == 2'b01 && rd_amatch == 0)
		begin
			match <= { match[95:0], a_word[31:0] };
			matchv <= { matchv[2:0], 1'b1 };
		end
	end
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
	case(matchv)
	4'b0000: begin end
	4'b0001: begin end
	4'b0011: begin end
	4'b0111: begin end
	4'b1111: begin end
	default: assert(0);
	endcase
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output: r_*, The (final, compressed) output read word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	r_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_stb <= 1'b0;
	else if (!o_stb || !r_busy)
		r_stb <= a_stb;

	// r_word (r_matched)
	// {{{
	initial r_matched = 1;
	always @(posedge i_clk)
	begin
		if (a_stb && !r_busy)
		begin
			// {{{
			r_matched <= (a_word[34:33] != 2'b01)
				|| rd_small || (|rd_amatch);
			r_word  <= a_word;
			r_value <= a_word[31:0];

			if (rd_bigger)
				r_word[34:14] <= { 5'b01111, a_word[15:0] };
			if (rd_small)
				r_word[34:21] <= { 5'b01110, a_word[8:0] };

			if (a_word[34:33] == 2'b01) casez(rd_amatch)
			4'b???1: r_word[34:28] <= 7'b01100_00;
			4'b??10: r_word[34:28] <= 7'b01100_01;
			4'b?100: r_word[34:28] <= 7'b01100_10;
			4'b1000: r_word[34:28] <= 7'b01100_11;
			default: begin end
			endcase
			// }}}
		end else if (i_busy && r_stb && !r_matched)
		begin
			if (table_match)
			begin
				r_matched <= 1'b1;
				r_word[34:21] <= tbl_word;
			end
		end else if (!i_busy)
		begin
			r_matched <= 1'b1;
		end

		if (i_reset)
			r_matched <= 1'b1;
	end
	// }}}

	// tbl_full, tbl_base
	// {{{
	initial	{ tbl_full, tbl_base } = 0;
	always @(posedge i_clk)
	if (i_reset)
		{ tbl_full, tbl_base } <= 0;
	else if (a_stb && !r_busy && a_word[34:33] == 2'b00)
		{ tbl_full, tbl_base } <= 0;
	else if (r_stb && !r_busy)
	begin
		if (!r_matched)
		begin
			{ tbl_full, tbl_base } <= tbl_base + 1;

			// tbl_full is sticky.  If set, leave it set.
			if (tbl_full)
				tbl_full <= 1'b1;
		end

		// On any address ACK -- clear the table
		//	Since any new connection will start by setting an
		//	address.  Hence, we clear our codebook at that time.
		// if (r_word[34:33] == 2'b00)
		//	{ tbl_full, tbl_base } <= 0;

		// On any reset ACK -- clear the table
		if ((r_word[34:33] == 2'b11)&&(r_word[30:29] == 2'b00))
			{ tbl_full, tbl_base } <= 0;
	end
	// }}}

	// Write to tbl_mem
	// {{{
	always @(posedge i_clk)
	if (r_stb && !r_busy && !r_matched)
		tbl_mem[tbl_base] <= r_value;
`ifdef	FORMAL
	always @(*)
	if (r_stb && !r_matched)
		assert(r_word[34:32] == 3'b010 || r_word[34:30] == 5'b01111);
	always @(*)
	if (r_stb && r_word[34:32] == 3'b010)
		assert(r_word[31:0] == r_value);
`endif
	// }}}

	// TBL.1: tbl_read_index
	// {{{
	initial	tbl_read_index = 0;
	always @(posedge i_clk)
	if (i_reset)
		tbl_read_index <= 0;
	else if (r_stb && !r_matched && !r_busy)
		// This word is done.  It didn't match anything.  Therefore,
		// we're writing it to the table.  Advance the read index
		// by one
		tbl_read_index <= tbl_base - 1;
	else if (!r_stb || !r_busy || r_matched)
	begin
		// Reset pointer, with no impact to the table
		tbl_read_index <= tbl_base - 2;
	end else if (!table_match && !r_matched
				&& (tbl_read_index[8:0] != tbl_base[8:0])
				&& (!tbl_read_index[9] || tbl_full))
		tbl_read_index <= tbl_read_index - 1;
`ifdef	FORMAL
	// {{{
	reg	[8:0]	f_ckindex;
	always @(*)
		f_ckindex = tbl_read_index + 2;

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin end else if ($past(r_stb && r_word[34:33] == 2'b11
						&& r_word[30:29] == 2'b00))
	begin end else if ($past(r_stb && r_word[34:33] == 2'b00))
	begin end else if ($past(a_stb && a_word[34:33] == 2'b00))
	begin end else if (r_stb && ($changed(tbl_base) || $past(r_stb && !i_busy)))
		assert(f_ckindex == tbl_base);
	// }}}
`endif
	// }}}

	// TBL.2: tbl_rdvalue <= tbl_mem[tbl_read_index]
	// {{{
	always @(posedge i_clk)
	if (tbl_reading)
		tbl_rdvalue <= tbl_mem[tbl_read_index[8:0]];
	// }}}

	// TBL.2: tbl_rdindex
	// {{{
	always @(posedge i_clk)
	if (tbl_reading)
		tbl_rdindex <= tbl_base - tbl_read_index[8:0] - 1;
	// }}}

	// TBL.2: tbl_valid
	always @(posedge i_clk)
		tbl_valid <= (r_stb && r_word[34:33] == 2'b01) && i_busy
			&& tbl_reading && (!tbl_read_index[9] || tbl_full);

	// TBL.3: table_match
	initial	table_match = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		table_match <= 1'b0;
	else if (!r_stb || !i_busy || r_matched)
		table_match <= 1'b0;
	else
		table_match <= tbl_valid && (r_value == tbl_rdvalue);

	// TBL.3: tbl_word
	always @(posedge i_clk)
	begin
		tbl_word <= 0;
		tbl_word[8:0] <= tbl_rdindex[8:0];
		tbl_word[13:9] <= 5'b01101;
	end

	always @(*)
	begin
		o_stb = r_stb;
		o_word = r_word;
	end

	assign	r_busy = o_stb && i_busy;
	assign	tbl_reading = 1;
	// }}}

	assign	o_active = ack_stb || a_stb;

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, diff_addr };
	// Verilator lint_on  UNUSED
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
	(* anyconst *)	reg	[31:0]	f_nvraddr, f_nvrdata;
	(* anyconst *)	reg	[8:0]	f_const_index;
	(* anyseq *)	reg		f_track_input;

	reg		f_rvknown;
	reg	[2:0]	f_tracking;
	reg	[34:0]	f_word;
	reg	[7:0]	fi_index, fc_index;
	reg	[31:0]	f_rvalue;
	reg	[34:0]	f_aword;
	reg	[31:0]	fc_addr, fc_diff;
	wire	[7:0]	f_ack;


	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	initial	fi_index = 0;
	always @(posedge i_clk)
	if (i_reset)
		fi_index <= 0;
	else if (i_stb && !o_busy)
		fi_index <= fi_index + 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Input/output raw stream properties
	// {{{

	// Stream property(ies)
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!i_stb);
	end else if ($past(i_stb && o_busy))
	begin
		assume(i_stb);
		assume($stable(i_word));
	end

	// Output stream property(ies)
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!o_stb);
	end else if ($past(o_stb && i_busy))
	begin
		assert(o_stb);
		if (o_word[34:33] != 2'b01)
		begin
			// All but read responses are stable
			assert($stable(o_word));
		end else if ($past(o_word[32:31]) == 2'b10)
		begin
			// Short compressed read responses are stable
			assert($stable(o_word));
		end else if ($past(o_word[32:30]) == 3'b110)
		begin
			// Longer compressed read responses are stable
			assert($stable(o_word));
		end
	end
	// }}}

	// Valid input word check
	// {{{
	always @(*)
	if (i_stb && !i_reset)
	begin
		case(i_word[34:33])
		2'b00: begin
			// Address
			assume(!i_word[32]); // Full address word only
			assume(i_word[31:0] != f_nvraddr);
			end
		2'b01: begin
			// Read response
			assume(!i_word[32]);
			assume(i_word[31:0] != f_nvrdata);
			end
		2'b10: // Write acknowledgments
			assume(i_word[32:0] == 0);
		2'b11: // Special responses
			assume(i_word == { 2'b11, 2'b00, 3'h0, 28'h0 }
				|| i_word == { 2'b11, 2'b00, 3'h1, 28'h0 }
				|| i_word == { 2'b11, 2'b00, 3'h2, 28'h0 }
				|| i_word == { 2'b11, 2'b00, 3'h3, 28'h0 });
		endcase
	end
	// }}}

	// Valid output word check
	// {{{
	always @(*)
	if (o_stb)
	begin
		case(o_word[34:33])
		2'b00: assert(o_word[32:0] != { 1'b0, f_nvraddr });
		2'b01: assert(o_word[32:0] != { 1'b0, f_nvrdata });
		2'b11: assert(o_word[32:31] == 2'b00);
		default: begin end
		endcase
	end
	// }}}

	// Contract word input check -- make sure it remains within bounds
	// {{{
	always @(*)
	if (|f_tracking)
	begin
		case(f_word[34:33])
		2'b00: begin // Address
			assert(!f_word[32]); // Full address word only
			assert(f_word[31:0] != f_nvraddr);
			end
		2'b01: begin // Read return data
			assert(!f_word[32]);
			assert(f_word[31:0] != f_nvrdata);
			end
		2'b10: assert(f_word[31:0] == 0); // Write acknowledgments
		2'b11: assert(f_word == { 2'b11, 2'b00, 3'h0, 28'h0 }
				|| f_word == { 2'b11, 2'b00, 3'h1, 28'h0 }
				|| f_word == { 2'b11, 2'b00, 3'h2, 28'h0 }
				|| f_word == { 2'b11, 2'b00, 3'h3, 28'h0 });
		endcase
	end
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract word tracking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//

	always @(*)
	if (i_reset || f_tracking != 0 || !i_stb)
		assume(!f_track_input);

	// f_tracking -- which stage of our compression pipeline is being trackd
	// {{{
	initial	f_tracking = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_tracking <= 0;
	else if (f_tracking == 0 && i_stb && !o_busy && f_track_input)
		f_tracking <= 1;
	else if (f_tracking[0])
	begin
		assert(ack_stb);
		assert(f_tracking[2:1] == 0);

		if (!a_stb || !a_busy)
			f_tracking <= 2;
	end else if (f_tracking[1])
	begin
		assert(a_stb);
		assert(f_tracking == 2);

		if (!r_stb || !i_busy)
			f_tracking <= 4;
	end else if (f_tracking[2])
	begin
		assert(r_stb);
		assert(f_tracking == 4);

		if (!i_busy)
			f_tracking <= 0;
	end
	// }}}

	// f_word -- which word are we tracking through the pipeline
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		f_word <= 0;
	else if (f_tracking == 0 && i_stb && !o_busy && f_track_input)
		f_word <= i_word;
	// }}}

	// fc_addr -- what was the last address when this word came in
	// {{{
	// Useful for verifying difference address returns
	always @(posedge i_clk)
	if (i_reset)
		fc_addr <= 0;
	else if (f_tracking == 0 && i_stb && !o_busy && f_track_input)
		fc_addr <= ack_addr;
	// }}}

	always @(posedge i_clk)
	if (i_reset)
		fc_index <= 0;
	else if (f_tracking == 0 && i_stb && !o_busy && f_track_input)
		fc_index <= fi_index;	// Index of our tracked (non-mem) value
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Address contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always  @(*)
	begin
		fc_diff[31:2] = f_word[31:2] - fc_addr[31:2];
		fc_diff[1:0] = 0;
	end

	always  @(*)
	if (ack_stb && ack_word[34:33] == 2'b00)
		assert(!ack_word[32] && ack_word[31:0] != f_nvraddr);

	always  @(*)
	if (a_stb && a_word[34:32] == 3'b000)
		assert(a_word[31:0] != f_nvraddr);

	always  @(*)
	if (r_stb && r_word[34:32] == 3'b000)
		assert(r_word[31:0] != f_nvraddr);

	always @(*)
	begin
		f_aword = f_word;
		if (f_aword[34:33] == 2'b00)
		begin
			// In order of priority from worst to best
			// 15-bit address: 00 1 11
			if ((&fc_diff[31:16])||(fc_diff[31:16] == 0))
				// Differential
				f_aword[34:14]= { 6'b001111, fc_diff[16:2] };
			if ((&f_word[31:16]) || (f_word[31:16] == 0))
				// Signed 14'bit
				f_aword[34:14] = { 6'b001110, f_word[16:2] };

			// 8'bit address: 00 1 10
			if ((&fc_diff[31:11])||(fc_diff[31:11] == 0))
				// Differential
				f_aword[34:21] = { 6'b001101, fc_diff[9:2] };
			if ((&f_word[31:11]) || (f_word[31:11] == 0))
				// Signed 10'bit
				f_aword[34:21] = { 6'b001100, f_word[9:2] };

			// 3'bit difference
			if ((&fc_diff[31:4])||(fc_diff[31:4] == 0))
				f_aword[34:28] = { 4'b0010, fc_diff[4:2] };
		end
	end


	always @(*)
	if (f_tracking != 0 && f_word[34:33] == 2'b00)
	begin
		if (f_tracking[0])
		begin
			assert(f_word[34:0] == ack_word[34:0]);
			assert(fc_diff == diff_addr);
		end
		if (f_tracking[1])
		begin
			assert(a_word[34:33] == 2'b00);
			casez(a_word[32:30])
			3'b0??: assert(f_word == a_word);
			3'b110: assert(f_aword[34:21] == a_word[34:21]);
			3'b111: assert(f_aword[34:14] == a_word[34:14]);
			default: begin end
			endcase
		end
		if (f_tracking[2])
		begin
			assert(r_word[34:33] == 2'b00);
			assert(r_matched);
			casez(r_word[32:30])
			3'b0??: begin cover(1); assert(f_word == r_word); end
			3'b110: begin cover(1); assert(f_aword[34:21] == r_word[34:21]); end
			3'b111: begin cover(1); assert(f_aword[34:14] == r_word[34:14]); end
			default: begin end
			endcase
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write ACK contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	f_ack = fi_index - fc_index - 8'h1;

	always @(*)
	if (f_tracking != 0 && f_word[34:33] == 2'b10)
	begin // on a write (ack) return ...
		if (f_tracking[0])
		begin
			assert(ack_word[34:33] == 2'b10);
			assert({ 3'h0, ack_word[32:28] } >= f_ack);
		end

		if (f_tracking[1])
			assert(a_word[34:33] == 2'b10);
		if (f_tracking[2])
		begin
			assert(r_word[34:33] == 2'b10);
			assert(r_matched);
		end
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Read response contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[8:0]	f_rddiff;

	// Assert f_nvrdata never ends up in our pipeline
	// {{{
	always  @(*)
	if (ack_stb && ack_word[34:33] == 2'b01)
		assert(!ack_word[32] && ack_word[31:0] != f_nvrdata);

	always  @(*)
	if (a_stb && a_word[34:33] == 2'b01)
		assert(!a_word[32] && a_word[31:0] != f_nvrdata);

	always  @(*)
	if (r_stb && r_word[34:32] == 3'b010)
		assert(r_word[31:0] != f_nvrdata);
	// }}}

	always @(posedge i_clk)
	if (r_stb && !i_busy && (tbl_base == f_const_index) && !r_matched)
		f_rvalue <= r_value;

	always @(*)
		f_rddiff = tbl_base - f_const_index-1;

	always @(*)
		// Is my special, chosen value, known
		f_rvknown = (tbl_base > f_const_index) || tbl_full;

	always @(*)
	if (f_rvknown)
	begin
		// if (r_stb && !r_busy && !r_matched)
		// tbl_mem[tbl_base] <= r_value;
		assert(tbl_mem[f_const_index] == f_rvalue);
	end

	always @(*)
	if (f_tracking[2] && f_word[34:33] != 2'b01)
		assert(r_matched);

	always @(*)
	if (!o_stb)
		assert(r_matched);

	always @(*)
	if (f_tracking != 0 && f_word[34:33] == 2'b01)
	begin	// Read response
		if (f_tracking[0])
			// Doesn't get changed in the first stage
			assert(f_word == ack_word);
		if (f_tracking[1])
			// Doesn't get changed in the second stage
			assert(f_word == a_word);
		if (f_tracking[2])
		begin
			assert(r_word[34:33] == 2'b01);
			if (!r_matched)
				assert(r_value == f_word[31:0]);
			casez(r_word[32:30])
			3'b0??: begin
				assert(r_word[31:0] == f_word[31:0]);
				assert(!r_matched);
				cover(1);
				end
			3'b100: begin
					assert(r_matched);
					// Quick 2b table lookup
					// Assertions are above
					cover(r_word[29:28] == 2'b00);
					cover(r_word[29:28] == 2'b01);
					cover(r_word[29:28] == 2'b10);
					cover(r_word[29:28] == 2'b11);
				end
			3'b101: begin
					assert(r_matched);
					if (f_rvknown && r_word[29:21] == f_rddiff)
					begin
						// Full table lookup
						assert(f_word[31:0] == f_rvalue);
						cover(1);
					end
				end
			3'b110:	begin
				// Small value
				assert(r_matched);
				assert(f_word <= 32'h00_00ff || f_word >= 32'hffff_ff80);
				assert(r_word[34:21] == { 5'b01110,
								f_word[8:0] });
				cover(1);
				end
			3'b111: begin
				// Bigger value
				// assert(r_matched);
				assert(f_word <= 32'h00_7fff || f_word >= 32'hffff_4000);
				assert(r_word[34:14] == { 5'b01111,
								f_word[15:0] });
				cover(1);
				end
			default: begin end
			endcase
		end
	end

	always @(*)
	if (f_tracking[1] && f_word[34:33] != 2'b01)
	begin
		assert(!rd_small);
		assert(!rd_bigger);
		// assert(rd_amatch == 0);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Special contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// The rule: Specials pass through without change

	always @(*)
	if (ack_stb && ack_word[34:33] == 2'b11)
		assert(ack_word[32:31] == 2'b00);

	always @(*)
	if (a_stb && a_word[34:33] == 2'b11)
		assert(a_word[32:31] == 2'b00);

	always @(*)
	if (r_stb && r_word[34:33] == 2'b11)
		assert(r_word[32:31] == 2'b00);

	always @(*)
	if (f_tracking != 0 && f_word[34:33] == 2'b11)
	begin
		if (f_tracking[0])
			assert(f_word[34:28] == ack_word[34:28]);
		if (f_tracking[1])
			assert(f_word[34:28] == a_word[34:28]);
		if (f_tracking[2])
		begin
			assert(r_word[34:28] == r_word[34:28]);
			assert(r_matched);
		end
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Activity check
	// {{{

	// Can only become active on an i_stb && !o_busy request
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_active);
	else if ($past(i_stb && !o_busy))
		assert(o_active);
	else if ($past(o_active))
		assert(o_active || o_stb);
	else
		assert(!o_active);

	// Can't generate an output without a prior o_active
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!o_active);
	else if ($past(i_stb && !o_busy))
		assert(o_active);
	else if (!$past(o_active) && !$past(o_stb))
		assert(!o_stb && !o_active);
	// }}}
`endif
// }}}
endmodule
