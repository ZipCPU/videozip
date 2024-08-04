////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exmkword.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To take a data stream, consisting of 7-bit input words, and to
//		pack it into a stream of 35-bit words.  (actually 34)
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
module	exmkword #(
		// {{{
		parameter [0:0]	OPT_EXTSYNC = 1'b0,
		parameter	INSZ=7,
		parameter	CWSZ=35,
		parameter	LGTIMEOUT = 20
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		input	wire			i_sync,
		// i_stb is true whenever new data is present
		input	wire			i_stb,
		output	wire			o_busy,
		input	wire	[(INSZ-1):0]	i_data,
		// o_stb is true whenever we have a valid word to send
		output	wire			o_stb,
		input	wire			i_busy,
		output	wire	[(CWSZ-1):0]	o_data,
		output	reg			o_reset_design,
		output	reg			o_reset_bridge,
		output	wire			o_active
		// }}}
	);

	// Local declarations
	// {{{
	reg			this_word;
	wire			sync;
	reg	[34:0]		sreg;
	reg	[2:0]		bytes_remaining, addr;
	// }}}

	// sync, sync_timer
	// {{{
	generate if (!OPT_EXTSYNC)
	begin : GEN_SYNC
		reg [LGTIMEOUT:0]	r_sync_timer;

		initial	r_sync_timer = 0;
		always @(posedge i_clk)
		if (i_reset || i_stb)
			r_sync_timer <= 0;
		else if (!r_sync_timer[LGTIMEOUT])
			r_sync_timer <= r_sync_timer + 1;


		assign	sync = (r_sync_timer[LGTIMEOUT] && !i_stb) || i_sync;
	end else begin : EXTERNAL_SYNC
		assign	sync = i_sync;
	end endgenerate
	// }}}

	// this_word, bytes_remaining
	// {{{
	initial	{ this_word, bytes_remaining } = 0;
	always @(posedge i_clk)
	if (i_reset || o_reset_bridge || sync)
		{ this_word, bytes_remaining } <= 0;
	else if (i_stb && !o_busy && bytes_remaining == 0)
	casez(i_data[6:2])
	// New address commands
	5'b000??: { this_word, bytes_remaining } <= { 1'b0, 3'h4 };
	5'b0010?: { this_word, bytes_remaining } <= { 1'b1, 3'h0 };
	5'b00110: { this_word, bytes_remaining } <= { 1'b0, 3'h1 };
	5'b00111: { this_word, bytes_remaining } <= { 1'b0, 3'h2 };
	// Write commands
	5'b010??: { this_word, bytes_remaining } <= { 1'b0, 3'h4 };
	5'b01100: { this_word, bytes_remaining } <= { 1'b1, 3'h0 };
	5'b01101: { this_word, bytes_remaining } <= { 1'b0, 3'h1 };
	5'b01110: { this_word, bytes_remaining } <= { 1'b0, 3'h1 };
	5'b01111: { this_word, bytes_remaining } <= { 1'b0, 3'h2 };
	// Read commands
	5'b100??: { this_word, bytes_remaining } <= { 1'b1, 3'h0 };
	5'b101??: { this_word, bytes_remaining } <= { 1'b0, 3'h1 };
	// Special commands
	5'b11???: { this_word, bytes_remaining } <= { 1'b1, 3'h0 };
	endcase else if (i_stb && !o_busy)
	begin
		if (bytes_remaining != 0)
			bytes_remaining <= bytes_remaining -1;
		this_word <= (bytes_remaining == 1);
	end else if (!o_stb || !i_busy)
		this_word <= 1'b0;
	// }}}

	// addr
	// {{{
	initial	addr = 0;
	always @(posedge i_clk)
	if (i_reset || o_reset_bridge || sync)
		addr <= 0;
	else if (this_word && !i_busy)
		addr <= (i_stb && !o_busy) ? 1:0;
	else if (i_stb && !o_busy)
		addr <= addr + 1;
	// }}}

	// sreg
	// {{{
	initial	sreg = 0;
	always @(posedge i_clk)
	if (i_reset || o_reset_bridge)
		sreg <= 0;
	else if (i_stb && !o_busy)
	begin
		if (sync || o_stb)
			sreg <= { i_data, 28'h0 };
		else if (i_stb && !o_busy)
		case(addr)
		3'h0:	sreg <= { i_data, 28'h0 };
		3'h1:	sreg <= { sreg[34:28], i_data, 21'h0 };
		3'h2:	sreg <= { sreg[34:21], i_data, 14'h0 };
		3'h3:	sreg <= { sreg[34:14], i_data,  7'h0 };
		3'h4:	sreg <= { sreg[34: 7], i_data };
		default: sreg <= 0;
		endcase
	end else if (o_stb && !o_busy)
		sreg <= 0;
	// }}}

	// o_stb
	// {{{
	assign	o_stb = this_word;
	// }}}

	// o_data
	// {{{
	assign	o_data = sreg;
	// }}}

	assign	o_busy   = o_stb && i_busy;
	assign	o_active = !o_stb && addr != 0;

	// o_reset_bridge, o_reset_design
	// {{{
	initial	o_reset_bridge = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_reset_bridge <= 1;
	else if (o_reset_bridge)
		o_reset_bridge <= 0;
	else
		o_reset_bridge <= (i_stb && !o_busy && addr == 0
			&& i_data[6:5] == 2'b11 && i_data[2:1] == 2'b00);

	initial	o_reset_design = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
		o_reset_design <= 1'b1;
	else if (o_reset_bridge)
		o_reset_design <= 1'b0;
	else
		o_reset_design <= (i_stb && !o_busy && addr == 0
			&& i_data[6:5] == 2'b11 && i_data[2:0] == 3'b000);
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

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (this_word)
		assert(bytes_remaining == 0);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_stb) && !$past(o_stb && i_busy))
		assert(!this_word);

	always @(*)
	if (o_reset_design)
		assert(o_reset_bridge);
	always @(*)
		assert(addr <= 5);

	always @(*)
	case(bytes_remaining)
	0: begin end
	1: assert(addr > 0 && addr <= 4);
	2: assert(addr > 0 && addr <= 3);
	3: assert(addr > 0 && addr <= 2);
	4: assert(addr == 1);
	default: assert(0);
	endcase

	always @(*)
	if (bytes_remaining == 0)
		assert(addr <= 5);

	always @(*)
	if (addr != 0 && bytes_remaining == 0)
		assert(this_word);

	always @(posedge i_clk)
	if (f_past_valid && !i_reset && $past(this_word && !i_reset) && addr == 0)
	begin
		cover($past(addr == 1));
		cover($past(addr == 2));
		cover($past(addr == 3));
		cover($past(addr == 5));
	end
`endif
// }}}
endmodule
