////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exidle.v
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
module	exidle #(
		// {{{
		parameter [0:0]	OPT_IDLE = 1'b1,	// Generate idle msgs
`ifdef	VERILATOR
		parameter	SHORT_LGIDLE = 15,
`else
		parameter	SHORT_LGIDLE = 20,
`endif
		parameter	LGIDLE = 25
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		i_stb,
		input	wire	[34:0]	i_word,
		input	wire		i_last,
		output	wire		o_busy,
		//
		input	wire	[1:0]	i_aux,
		input	wire		i_cts,
		input	wire		i_int,
		input	wire		i_fifo_err,
		//
		output	reg		o_stb,
		output	reg	[34:0]	o_word,
		output	reg		o_last,
		output	wire	[6:0]	o_null,
		input	wire		i_busy
		// }}}
	);

	// Local registers
	// {{{
	reg		last_err, r_last;
	reg		r_aux_flag;
	reg	[1:0]	last_aux;
	reg		r_int, last_int;
	reg		cts_flag;
	reg		fifo_err_flag;
	wire		trigger;
	reg		r_busy, outgoing_special;
	// }}}

	// Notes
	// {{{

	// 1. On a new word, send that word
	// 2. Else, on a FIFO error, send that FIFO error
	// 3. Else, on either an interrupt or a change in CTS,
	//	send an idle update
	// 4. Else on a timeout or change in i_aux, send an idle update
	//	Timeouts only change if/when OPT_IDLE
	//
	// If an idle response is queued, and a higher priority comes in,
	// the higher priority response is sent

	// This is broken ... how often do we send messages?
	// What if i_int toggles alternately?  Do we send it every chance we
	// get?  What about i_cts, if we are close to the edge?  How about
	// the FIFO error?  Should probably not send those at more than
	// 5Hz or so.
	// }}}

	// outgoing_special
	// {{{
	always @(*)
		outgoing_special = o_stb && !i_busy && o_word[34:33] == 2'b11;
	// }}}

	// FIFO Error tracking: last_err
	// {{{
	// Goal: set fifo_err_flag on every rise of i_fifo_err, clearing it on
	// transmit
	//
	// What throttles sending on fifo_err_flag

	// last_err
	initial	last_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_err <= 1'b0;
	else
		last_err <= i_fifo_err;

	initial	fifo_err_flag = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		fifo_err_flag <= 1'b0;
	else if (i_fifo_err && !last_err)
		fifo_err_flag <= 1'b1;
	else if (outgoing_special && o_word[30:28] == 3'b011)
		fifo_err_flag <= 1'b0;
	// }}}

	// AUX: r_aux_flag, last_aux
	// {{{
	// Goal: set r_aux_flag on every change of i_aux, clearing it on
	// transmit
	initial	last_aux = 2'b00;
	always @(posedge i_clk)
	if (i_reset)
		last_aux <= 2'b00;
	else
		last_aux <= i_aux;

	// r_aux_flag
	initial	r_aux_flag = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_aux_flag <= 1'b0;
	else if (last_aux != i_aux)
		r_aux_flag <= 1'b1;
	else if (outgoing_special)
		r_aux_flag <= 1'b0;
	// }}}

	// INT: r_int, last_int
	// {{{
	// Goal: set r_int on any rise of i_int, clearing it on transmit
	initial	last_int = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_int <= 1'b0;
	else
		last_int <= i_int;

	initial	r_int    = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_int <= 1'b0;
	else if (i_int && !last_int)
		r_int <= 1'b1;
	else if (outgoing_special && o_word[30] && o_word[28])
		r_int <= 1'b0;
	// }}}

	// cts_flag
	// {{{
	// Goal: send cts=0 on an idle if ever cts drops between idles
	initial	cts_flag = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		cts_flag <= 1'b0;
	else if (!i_cts)
		cts_flag <= 1'b1;
	else if (outgoing_special && o_word[30:29] == 2'b10)
		cts_flag <= 1'b0;
	// }}}

	// Idle timeout and trigger
	// {{{
	generate if (OPT_IDLE)
	begin : GEN_IDLE_TRIGGER
		reg			idle_timeout;
		reg	[LGIDLE-1:0]	idle_counter;
		reg	[3:0]		short_count;

		initial	short_count = 0;
		always @(posedge i_clk)
		if (i_reset)
			short_count <= 0;
		else if (o_stb && o_word[34:33] != 2'b11)
			short_count <= 0;
		else if (o_stb && !i_busy && !short_count[3])
			short_count <= short_count + 1;

		initial	{ idle_timeout, idle_counter } = 0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			idle_timeout <= 0;
			idle_counter <= -1 -(1<<SHORT_LGIDLE);
		end else if (i_stb)
		begin
			idle_timeout <= 0;
			idle_counter <= -1 -(1<<SHORT_LGIDLE);
		end else if (idle_timeout)
		begin
			if (!o_stb || !i_busy)
			begin
				idle_timeout <= 0;
				if (!short_count[3])
				begin
					// Use a short counter, send some quick
					// idles for synchronization, then
					// switch to the longer counter
					idle_counter <= -1 -(1<<SHORT_LGIDLE);
				end else
					idle_counter <= 0;
			end
		end else if (o_stb && ((o_word[34:33] != 2'b11)
							|| !short_count[3]))
		begin
			idle_timeout <= 0;
			if (o_word[34:33] == 2'b11 && short_count[3])
				idle_counter <= 0;
			else
				idle_counter <= -1 -(1<<SHORT_LGIDLE);
		end else // if (!idle_timeout)
			{ idle_timeout, idle_counter } <= idle_counter + 1;

		assign	trigger = idle_timeout||r_aux_flag||fifo_err_flag;
	end else begin : NO_IDLE_TRIGGER
		// We'll append to any message special AUX or ERR flags
		// as necessary
		assign	trigger = r_aux_flag||fifo_err_flag;
	end endgenerate
	// }}}

	// o_stb, o_word, r_busy, o_null
	// {{{
	assign	o_null = { 2'b11, i_aux, 1'b1, !cts_flag, r_int };

	initial	{ o_stb, o_word, r_busy } = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_stb <= 1'b0;
		o_word <= 0;
		o_last <= 1'b0;
		r_busy <= 1'b0;
		r_last <= 1'b0;
		// }}}
	end else if (i_stb && !o_busy)
	begin // Incoming data has the right of way
		// {{{
		o_stb  <= 1'b1;
		o_word <= i_word;
		o_last <= i_last && !trigger && !OPT_IDLE;
		r_last <= i_last &&  trigger && !OPT_IDLE;
		r_busy <= 1'b1;
		if (i_word[34:33] == 2'b11)
			o_word[32:31] <= i_aux;
		// }}}
	end else if ((OPT_IDLE && (!o_stb || !i_busy) && trigger)
		|| (!OPT_IDLE && r_last && !i_busy && trigger))
	begin // If there's  no data, we can send an idle cycle
		// {{{
		o_stb <= 1'b1;
		o_word <= 0;
		o_last <= 1'b1;
		r_last <= !r_aux_flag || !fifo_err_flag;

		// IDLE word
		o_word[34:28] <= o_null;
		if (fifo_err_flag && (!o_stb || o_word[34:31] != o_null[6:3]
						|| o_word[30:28] != 3'b011))
			// Send a FIFO error flag, but *ONLY* if it's not
			// already being sent.
			o_word[30:28] <= 3'b011;
		r_busy <= 1'b0;
		// }}}
	end else if (!i_busy)
		o_stb <= 0;
	// }}}

	assign	o_busy   = r_busy && i_busy;
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

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		// assume(!i_stb);
		// Not necessarily true.
	end else if ($past(i_stb && o_busy))
	begin
		assume(i_stb);
		assume($stable(i_word));
	end

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!o_stb);
		assume(!i_stb);
	end else if ($past(o_stb && i_busy))
	begin
		assert(o_stb);
		if ($past(r_busy))
			assert($stable(o_word));
	end

	always @(*)
	if (o_stb && o_word[34:33] != 2'b11)
		assert(r_busy);
	// always @(*) if (r_busy) assert(o_stb && o_word[34:33] != 2'b11);
`endif
// }}}
endmodule
