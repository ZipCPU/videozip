////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/exbus/exwb.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Actually drive the bus for the EX debugging bus, returning
//		responses from the bus (ACK, value, error, etc.) to the
//	processing pipeline.
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
module	exwb #(
		// {{{
		parameter	ADDRESS_WIDTH=30,
		localparam	AW=ADDRESS_WIDTH, // Shorthand for address width
				CW=35,	// Command word width
		parameter [0:0]	OPT_PIPELINED = 1'b1,
		parameter [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk, i_reset,
		// The input command channel
		// {{{
		input	wire			i_cmd_stb,
		input	wire	[CW-1:0]	i_cmd_word,
		output	wire			o_cmd_busy,
		// }}}
		// The return command channel
		// {{{
		output	reg			o_cmd_stb,
		output	reg	[CW-1:0]	o_cmd_word,
		// }}}
		// Our wishbone outputs
		// {{{
		output	reg			o_wb_cyc,
		output	reg			o_wb_stb,
		output	reg			o_wb_we,
		output	reg	[AW-1:0]	o_wb_addr,
		output	reg	[31:0]		o_wb_data,
		output	wire	[3:0]		o_wb_sel,
		// }}}
		// Wishbone return inputs
		input	wire		i_wb_stall, i_wb_ack,
		input	wire	[31:0]	i_wb_data,
		input	wire		i_wb_err
		// }}}
	);

	// Local declarations
	// {{{
	wire	[12:0]	outstanding;

	localparam	[1:0]	CMD_SUB_ADDR    = 2'b00,
				CMD_SUB_WR      = 2'b01,
				CMD_SUB_RD	= 2'b10;
				// CMD_SUB_SPECIAL = 2'b11;

	localparam	[2:0]	RSP_SUB_DATA    = 3'b010,	// Read data
				RSP_SUB_ACK     = 3'b100,	// Write ack
				RSP_SUB_SPECIAL	= 3'b110,
				RSP_SUB_ADDR    = 3'b000;

	localparam [34:0] RSP_WRITE_ACKNOWLEDGEMENT = { RSP_SUB_ACK, 32'h0 },
			RSP_RESET = { RSP_SUB_SPECIAL, 4'h0, 28'h00 },
			RSP_BUS_ERROR =	{ RSP_SUB_SPECIAL, 4'h2, 28'h00 };
	localparam	ADRDIF_BIT = 32;

	reg		newaddr, inc;
	wire		last_ack;
	reg	[11:0]	read_count;

	//
	// Decode our input commands
	// {{{
	wire	i_cmd_addr, i_cmd_wr, i_cmd_bus, i_cmd_rd;

	assign	i_cmd_addr = (i_cmd_stb)&&(i_cmd_word[34:33] == CMD_SUB_ADDR);
	assign	i_cmd_rd   = (i_cmd_stb)&&(i_cmd_word[34:33] == CMD_SUB_RD);
	assign	i_cmd_wr   = (i_cmd_stb)&&(i_cmd_word[34:33] == CMD_SUB_WR);
	assign	i_cmd_bus  = (i_cmd_stb)&&(i_cmd_word[34:33] == CMD_SUB_WR
					|| i_cmd_word[34:33] == CMD_SUB_RD);
	// }}}
	// }}}

	// o_wb_cyc, o_wb_stb
	// {{{
	// These two linse control our state
	initial	o_wb_cyc = 1'b0;
	initial	o_wb_stb = 1'b0;
	always @(posedge i_clk)
	if (i_reset || (i_wb_err && o_wb_cyc))
	begin
		// On any error or reset, then clear the bus.
		o_wb_cyc   <= 1'b0;
		o_wb_stb   <= 1'b0;
		read_count <= 0;
	end else if (o_wb_stb)
	begin
		//
		// BUS REQUEST state
		//
		if (!i_wb_stall)
		begin
			if (read_count > 1)
				o_wb_stb <= 1;
			else
				// If we are only going to do one transaction,
				// then as soon as the stall line is lowered,
				// we are done.
				o_wb_stb <= OPT_PIPELINED && i_cmd_bus && !o_cmd_busy;
			if (read_count > 0)
				read_count <= read_count - 1;
		end

		// While not likely, it is possible that a slave might ACK
		// our request on the same clock it is received.  In that
		// case, drop the CYC line.
		//
		// We gate this with the stall line in case we receive an
		// ACK while our request has yet to go out.  This may make
		// more sense later, when we are sending multiple back to back
		// requests across the bus, but we'll leave this gate here
		// as a placeholder until then.
		if (!i_wb_stall && i_wb_ack)
			o_wb_cyc <= (read_count > 1)
				|| OPT_PIPELINED && (!last_ack
					|| (i_cmd_bus && !o_cmd_busy));
	end else if (o_wb_cyc)
	begin
		//
		// BUS WAIT
		//
		if (i_wb_ack)
			// Once the slave acknowledges our request, we are done.
			o_wb_cyc <= OPT_PIPELINED && (!last_ack
					|| (i_cmd_bus && !o_cmd_busy));
	end else begin
		//
		// IDLE state
		//
		read_count <= 0;
		if (i_cmd_bus)
		begin
			// We've been asked to start a bus cycle from our
			// command word, either RD or WR
			o_wb_cyc <= 1'b1;
			o_wb_stb <= 1'b1;

			if (i_cmd_word[34:33] == CMD_SUB_RD)
				read_count <= i_cmd_word[11:0];
		end
	end
	// }}}

	// o_cmd_busy
	// {{{
	generate if (OPT_PIPELINED)
	begin : MULTIPLE_ISSUE

		reg	[12:0]	r_outstanding;
		reg		r_cmd_busy;

		initial	r_outstanding = 0;
		always @(posedge i_clk)
		if (i_reset || (o_wb_cyc && i_wb_err))
			r_outstanding <= 0;
		else if (i_cmd_wr && !o_cmd_busy)
		begin
			r_outstanding <= r_outstanding + 1
					- ((o_wb_cyc && i_wb_ack) ? 1:0);
		end else if (i_cmd_rd && !o_cmd_busy)
		begin
			r_outstanding <= r_outstanding + i_cmd_word[11:0]
					- ((o_wb_cyc && i_wb_ack) ? 1:0);
		end else if (o_wb_cyc && i_wb_ack)
			r_outstanding <= r_outstanding - 1;

		assign	outstanding = r_outstanding;

		assign	last_ack = (outstanding <= 1);

		always @(*)
		if (!o_wb_cyc)
			r_cmd_busy = 1'b0;
		else if (!o_wb_stb)
			r_cmd_busy = 1'b1;
		else if (read_count > 0)
			r_cmd_busy = 1'b1;
		else if (i_wb_stall)
			r_cmd_busy = 1'b1;
		else if (&outstanding)
			r_cmd_busy = 1'b1;
		else
			r_cmd_busy = i_cmd_word[34:33] == 2'b11
					|| (i_cmd_wr != o_wb_we);

		assign	o_cmd_busy = r_cmd_busy;

	end else begin : SIMPLE_ISSUE
		// For now, we'll use the bus cycle line as an indication of
		// whether or not we are too busy to accept anything else from
		// the command port.  This will change if we want to accept
		// multiple write commands per bus cycle, but that will be a
		// bus master that's not nearly so simple.
		assign	o_cmd_busy = o_wb_cyc;

		assign	last_ack = 1;

		assign	outstanding = (o_wb_cyc ? 1:0);

	end endgenerate
	// }}}

	// o_wb_we
	// {{{
	// The bus WE (write enable) line, governing wishbone direction
	//
	// We'll never change direction mid bus-cycle--at least not in this
	// implementation (atomic accesses may require it at a later date). 
	// Hence, if CYC is low we can set the direction.
	always @(posedge i_clk)
	if (!o_wb_cyc && !o_cmd_busy && (!OPT_LOWPOWER || i_cmd_bus))
		o_wb_we <= i_cmd_wr;
	// }}}

	// o_wb_addr, newaddr
	// {{{
	// The bus ADDRESS lines
	//
	initial	newaddr = 1'b0;
	always @(posedge i_clk)
	begin
		if (i_cmd_addr && !o_cmd_busy)
		begin
			// {{{
			// If we are in the idle state, we accept address
			// setting commands.  Specifically, we'll allow the
			// user to either set the address, or add a difference
			// to our address.  The difference may not make sense
			// now, but if we ever wish to compress our command bus,
			// sending an address difference can drastically cut
			// down the number of bits required in a set address
			// request.
			if (!i_cmd_word[ADRDIF_BIT])
				o_wb_addr <= i_cmd_word[AW+1:2];
			else
				o_wb_addr <= i_cmd_word[AW+1:2] + o_wb_addr;

			//
			// We'll allow that bus requests can either increment
			// the address, or leave it the same.  One bit in the
			// command word will tell us which, and we'll set this
			// bit on any set address command.
			inc <= i_cmd_word[0];
			// }}}
		end else if (o_wb_stb && !i_wb_stall)
			// The address lines are used while the bus is active,
			// and referenced any time STB && !STALL are true.
			//
			// However, once STB and !STALL are both true, then the
			// bus is ready to move to the next request.  Hence,
			// we add our increment (one or zero) here.
			o_wb_addr <= o_wb_addr + { {(AW-1){1'b0}}, inc };


		// We'd like to respond to the bus with any address we just
		// set.  The goal here is that, upon any read from the bus,
		// we should be able to know what address the bus was set to.
		// For this reason, we want to return the bus address up the
		// command stream.
		//
		// The problem is that the add (above) when setting the address
		// takes a clock to do.  Hence, we'll use "newaddr" as a flag
		// that o_wb_addr has a new value in it that needs to be
		// returned via the command link.
		if (i_cmd_addr && !o_cmd_busy)
			newaddr <= 1;
		else if (i_cmd_bus)
			newaddr <= 0;
	end
	// }}}

	// o_wb_data: The bus DATA (output) lines
	// {{{
	always @(posedge i_clk)
	begin
		// This may look a touch confusing ... what's important is that:
		//
		// 1. No one cares what the bus data lines are, unless we are
		//	in the middle of a write cycle.
		// 2. Even during a write cycle, these lines are don't cares
		//	if the STB line is low, indicating no more requests
		// 3. When a request is received to write, and so we transition
		//	to a bus write cycle, that request will come with data.
		// 4. Hence, we set the data words in the IDLE state on the
		//	same clock we go to BUS REQUEST.  While in BUS REQUEST,
		//	these lines cannot change until the slave has accepted
		//	our inputs.
		//
		// Thus we force these lines to be constant any time STB and
		// STALL are both true, but set them otherwise.
		//
		if ((!OPT_LOWPOWER || (i_cmd_wr && !o_cmd_busy))
					&& (!o_wb_stb || !i_wb_stall))
			o_wb_data <= i_cmd_word[31:0];
	end
	// }}}

	// o_wb_sel
	// {{{
	// For this command bus channel, we'll only ever direct word addressing.
	//
	assign	o_wb_sel = 4'hf;
	// }}}

	// o_cmd_stb, o_cmd_word
	// {{{
	// The COMMAND RESPONSE return channel
	//
	// This is where we set o_cmd_stb and o_cmd_word for the return channel.
	// The logic is set so that o_cmd_stb will be true for any one clock
	// where we have data to reutrn, and zero otherwise.  If o_cmd_stb is
	// true, then o_cmd_word is the response we want to return.  In all
	// other cases, o_cmd_word is a don't care.
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_cmd_stb <= 1'b1;
		o_cmd_word <= RSP_RESET;
	end else if (o_wb_cyc)
	begin
		//
		// We're either in the BUS REQUEST or BUS WAIT states
		//
		// Either way, we want to return a response on our command
		// channel if anything gets ack'd
		o_cmd_stb <= (i_wb_ack || i_wb_err);
		//
		//
		if (i_wb_err)
			o_cmd_word <= RSP_BUS_ERROR;
		else if (o_wb_we)
			o_cmd_word <= RSP_WRITE_ACKNOWLEDGEMENT;
		else if (!OPT_LOWPOWER || i_wb_ack)
			o_cmd_word <= { RSP_SUB_DATA, i_wb_data };
	end else begin
		o_cmd_stb <= 0;
		//
		// We are in the IDLE state.
		//
		// Echo any new addresses back up the command chain
		//
		if (i_cmd_stb && i_cmd_word[34:33] == 2'b11)
		begin
			o_cmd_stb  <= 1'b1;
			o_cmd_word <= i_cmd_word;
		end else if (i_cmd_bus)
		begin
			o_cmd_stb  <= newaddr;
			if (!OPT_LOWPOWER || newaddr)
				o_cmd_word <= { RSP_SUB_ADDR, {(30-AW){1'b0}},
					o_wb_addr, 1'b0, inc };
		end
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal methods
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	localparam	F_LGDEPTH = 12;
	wire	[F_LGDEPTH-1:0]	f_nreqs, f_nacks, f_outstanding;
	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Input command channel properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid  || $past(i_reset))
	begin
		assume(!i_cmd_stb);
	end else if ($past(i_cmd_stb && o_cmd_busy))
	begin
		assume(i_cmd_stb);
		assume($stable(i_cmd_word));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Bus properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	fwb_master #(
		// {{{
		.AW(AW), .DW(32), .F_OPT_SOURCE(1'b1)
		// }}}
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		//
		.i_wb_cyc(o_wb_cyc), .i_wb_stb(o_wb_stb), .i_wb_we(o_wb_we),
			.i_wb_addr(o_wb_addr),
			.i_wb_data(o_wb_data),.i_wb_sel(o_wb_sel),
		.i_wb_ack(i_wb_ack), .i_wb_stall(i_wb_stall),
			.i_wb_idata(i_wb_data), .i_wb_err(i_wb_err),
		.f_nreqs(f_nreqs), .f_nacks(f_nacks),
			.f_outstanding(f_outstanding)
		// }}}
	);

	always @(*)
	if (i_cmd_rd)
		assume(i_cmd_word[11:0] != 0);

	always @(*)
	if (f_past_valid && read_count > 0)
		assert(o_wb_stb && !o_wb_we);

	generate if (OPT_PIPELINED)
	begin
		always @(*)
		if (o_wb_cyc)
		begin
			if (o_wb_we)
			begin
				assert(f_outstanding + (o_wb_stb ? 1:0) == outstanding);
				assert(read_count == 0);
			end else begin
				assert(!o_wb_stb || read_count > 0);
				assert(f_outstanding + read_count == outstanding);
			end
		end else assert(!f_past_valid || read_count == 0);
	end else begin
		always @(*)
			assert(outstanding == o_wb_cyc);
	end endgenerate

	always @(*)
	if (!o_wb_cyc)
		assert(outstanding == 0);

	always @(*)
	if (((f_outstanding == 0) || (outstanding == 0)) && !o_wb_stb)
		assert(!o_wb_cyc);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset)
			&& $past(i_cmd_bus && !o_cmd_busy && !i_wb_err))
	begin
		assert(o_wb_cyc);
		assert(o_wb_stb);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Return channel properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (!f_past_valid)
	begin end
	else if ($past(i_reset))
	begin
		assert(o_cmd_stb);
		assert(o_cmd_word == RSP_RESET);
	end else if ($past(o_wb_cyc && i_wb_err))
	begin
		assert(o_cmd_stb);
		assert(o_cmd_word == RSP_BUS_ERROR);
	end else if ($past(o_wb_cyc && i_wb_ack))
	begin
		assert(o_cmd_stb);
		if (o_wb_we)
			assert(o_cmd_word == RSP_WRITE_ACKNOWLEDGEMENT);
		else
			assert(o_cmd_word== { RSP_SUB_DATA, $past(i_wb_data) });
	end else if ($past(o_wb_cyc))
		assert(!o_cmd_stb);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin end
	else if ($past(i_cmd_stb && !o_cmd_busy && i_cmd_word[34:33] == 2'b11))
	begin
		// Special commands are simply passed through
		assert(o_cmd_stb);
		assert(o_cmd_word == $past(i_cmd_word));
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) lowpower properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge i_clk)
	if (OPT_LOWPOWER && f_past_valid && !$past(i_reset) && (!o_wb_stb
				|| ($past(o_wb_stb && i_wb_stall))))
	begin
		if (!$past(i_wb_err))
			assert($stable(o_wb_data));
		assert($stable(o_wb_we));
		assert($stable(o_wb_sel));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover  checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[3:0]	cvr_writes, cvr_reads;

	initial	cvr_writes = 0;
	always @(posedge i_clk)
	if (i_reset || i_wb_err)
		cvr_writes <= 0;
	else if (o_wb_cyc && o_wb_we && i_wb_ack && !cvr_writes[3])
		cvr_writes <= cvr_writes + 1;

	initial	cvr_reads = 0;
	always @(posedge i_clk)
	if (i_reset || i_wb_err)
		cvr_reads <= 0;
	else if (o_wb_cyc && !o_wb_we && i_wb_ack && !cvr_reads[3])
		cvr_reads <= cvr_reads + 1;

	always @(*)
	if (!i_reset && !i_wb_err)
	begin
		cover(cvr_writes[3]);
		cover(cvr_reads[3]);
	end

	// }}}
`endif
// }}}
endmodule
