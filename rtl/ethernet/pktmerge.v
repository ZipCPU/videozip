////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/pktmerge.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Given several signal sources, merge and create an output signal
//		source from the various input.
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
module	pktmerge #(
		// {{{
		parameter	NS = 4,
		parameter	DW = 32
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire	[NS-1:0]	S_AXIN_VALID,
		output	wire	[NS-1:0]	S_AXIN_READY,
		input	wire	[NS*DW-1:0]	S_AXIN_DATA,
		input	wire	[NS-1:0]	S_AXIN_LAST,
		input	wire	[NS-1:0]	S_AXIN_ABORT,
		//
		output	wire			M_AXIN_VALID,
		input	wire			M_AXIN_READY,
		output	wire	[8-1:0]		M_AXIN_DATA,
		output	wire			M_AXIN_LAST,
		output	wire			M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	reg			packet_in_progress;
	wire			arbiter_stall;
	reg	[DW-1:0]	next_data;
	reg			next_last;
	integer			ik;
	wire	[NS-1:0]	arb_grant;
	//
	// r_* stage
	reg			r_valid, r_abort, r_last;
	wire			r_ready;
	reg	[DW-1:0]	r_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Pick a packet and accept it into our system
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// packet_in_progress, arbiter_stall
	// {{{
	initial	packet_in_progress = 1'b0;
	always @(posedge i_clk)
	begin
		if (arb_grant == 0)
			// If there's no grant, there can be no packet in
			// progress.  On the other hand, we are *guaranteed*
			// a packet grant if there's ever a request and it
			// isn't stalled.
			packet_in_progress <= |S_AXIN_VALID;
		else if (|(arb_grant & S_AXIN_VALID & ~S_AXIN_READY))
			// If the channel is stalled, we remain a packet in
			// progress
			packet_in_progress <= 1'b1;
		else if (|(arb_grant & S_AXIN_VALID & S_AXIN_READY))
			// Once a packet either completes or aborts, there is
			// no longer any packet in progress
			packet_in_progress <= (|(arb_grant & ~S_AXIN_LAST & ~S_AXIN_ABORT));
		else if (|(arb_grant& ~S_AXIN_VALID & S_AXIN_ABORT))
			// On any abort, there is no longer any packet in
			// progress
			packet_in_progress <= 1'b0;

		if (i_reset)
			packet_in_progress <= 1'b0;
	end

	assign	arbiter_stall = packet_in_progress;
	/*
		// If the channel is stalled, the arbiter must stall
		(|(arb_grant & (S_AXIN_VALID & ~S_AXIN_READY)))
		// We're not stalled if the channel steps forward on the
		//   last beat of a packet
		|| (|(arb_grant & (S_AXIN_VALID & S_AXIN_READY
					& ~S_AXIN_LAST & ~S_AXIN_ABORT)))
		// We're not stalled if the packet aborts w/ !VALID
		|| (|(arb_grant & (~S_AXIN_VALID & S_AXIN_ABORT)));
	*/
	// }}}

	// Round Robin arbiter
	// {{{
	pktarbiter #(.W(NS)
	) u_pktarbiter (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		//
		.i_req(S_AXIN_VALID & ~S_AXIN_ABORT),
		.i_stall(arbiter_stall),
		.o_grant(arb_grant)
		// }}}
	);
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// r_* stage: At width DW
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// r_valid
	// {{{
	initial	r_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_valid <= 1'b0;
	else if (!r_valid || r_ready)
		r_valid <= |(S_AXIN_VALID & ~S_AXIN_ABORT & S_AXIN_READY);
`ifdef	FORMAL
	always @(*)
	if (!i_reset && |S_AXIN_READY)
		assert((S_AXIN_READY & ~arb_grant) == 0);
`endif
	// }}}

	// next_data, next_last
	// {{{
	always @(*)
	begin
		next_data = 0;
		next_last = 0;

		for(ik=0; ik<NS; ik=ik+1)
		if (arb_grant[ik])
		begin
			next_data = next_data | S_AXIN_DATA[ik * DW +: DW];
			next_last = next_last | S_AXIN_LAST[ik];
		end
	end
	// }}}

	// r_data, r_last
	// {{{
	always @(posedge i_clk)
	if (!r_valid || r_ready)
	begin
		r_data <= next_data;
		r_last <= next_last;
	end
	// }}}

	// r_abort
	// {{{
	initial	r_abort = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_abort <= 1'b0;
	else if (!r_abort && |(arb_grant & S_AXIN_ABORT))
		r_abort <= 1'b1;
	else if (!r_valid || r_ready)
		r_abort <= 1'b0;
	// }}}

	assign	S_AXIN_READY = (packet_in_progress && (!r_valid || r_ready))
						? arb_grant : 0;

`ifdef	FORMAL
	always @(*)
	if (!packet_in_progress)
		assert(!r_valid || r_last);

	always @(*)
	if (r_valid && !r_last)
		assert(packet_in_progress);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// M_AXIN_* stage: At width 8
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	generate if (DW == 8)
	begin : GEN_NO_SIZE_CHANGE

		assign	M_AXIN_VALID = r_valid;
		assign	r_ready = M_AXIN_READY;
		assign	M_AXIN_DATA  = r_data;
		assign	M_AXIN_LAST  = r_last;
		assign	M_AXIN_ABORT = r_abort;

	end else begin : GEN_DOWNSIZE

		reg				m_valid, m_last, m_abort;
		reg	[$clog2(DW/8)-1:0]	m_state;
		reg	[DW-1:0]		sreg_data;
		reg				sreg_last;

		// m_valid, m_state
		// {{{
		initial	m_valid = 1'b0;
		initial	m_state = 0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			m_valid <= 1'b0;
			m_state <= 0;
		end else if (!M_AXIN_VALID || M_AXIN_READY)
		begin
			if (r_valid || m_state > 0)
				m_state <= m_state - 1;
			m_valid <= (r_valid && !r_abort) || m_state != 0;
			// m_abort <= (m_state == 0 || !sreg_last) && r_abort;

			if (m_abort || (r_abort && m_valid && m_state == 0 && m_last))
			begin
				// Deskcheck review ...why the condition above??
				m_valid <= 0;
				m_state <= 0;
			end
		end
		// }}}

		// sreg_data, sreg_last
		// {{{
		initial	sreg_last = 1'b0;
		always @(posedge i_clk)
		begin
			if (r_valid && r_ready)
			begin
				sreg_data <= r_data;
				sreg_last <= r_last;
			end else if (!M_AXIN_VALID || M_AXIN_READY)
			begin
				sreg_data <= sreg_data << 8;
				if (m_state == 0)
					sreg_last <= 1'b0;
			end

			if (i_reset || m_abort || (m_state == 0 && r_abort))
				sreg_last <= 1'b0;
		end
		// }}}

		// m_last
		// {{{
		initial	m_last = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			m_last <= 1'b0;
		else if (!M_AXIN_VALID || M_AXIN_READY)
			m_last <= sreg_last && (m_state == 1);
`ifdef	FORMAL
		always @(*)
		if (!M_AXIN_ABORT)
		begin
			if (m_state != 0)
				assert(!m_last);
			else
				assert(m_last == sreg_last);
		end

		always @(posedge i_clk)
		if (!i_reset && $fell(M_AXIN_VALID) && $past(M_AXIN_ABORT))
			assert(!M_AXIN_ABORT);
`endif
		// }}}

		// m_abort
		// {{{
		// Only abort if we haven't already committed to the last word
		initial	m_abort = 1'b0;
		always @(posedge i_clk)
		if (i_reset)
			m_abort <= 1'b0;
		else if (!M_AXIN_VALID || M_AXIN_READY)
		begin
			m_abort <= 0;
			if (!M_AXIN_VALID || !M_AXIN_ABORT)
				m_abort <= (m_state == 0 || !sreg_last) && r_abort;
		end else if (r_abort&& (m_state == 0 || !sreg_last))
			m_abort <= 1'b1;
		// }}}

		assign	M_AXIN_VALID = m_valid;
		assign	M_AXIN_DATA  = sreg_data[DW-1:DW-8];
		assign	M_AXIN_LAST  = m_last;
		assign	M_AXIN_ABORT = m_abort;

		assign	r_ready = ((!M_AXIN_VALID || M_AXIN_READY)
						&& m_state == 0)
				||(r_abort && m_abort)
				||(r_valid && r_abort && sreg_last);

`ifdef	FORMAL
		always @(*)
		if (M_AXIN_VALID && !M_AXIN_ABORT && !m_last) // sreg_last == 0)
			assert((m_state > 0 && sreg_last)
				|| (r_valid && r_last) || packet_in_progress);

		always @(*)
		if (!r_valid && !packet_in_progress)
			assert(!M_AXIN_VALID || M_AXIN_ABORT || sreg_last != 0);
`endif
	end endgenerate

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
	// Local declarations
	// {{{
	reg	f_past_valid;
	genvar	gk;
	wire	[10:0]		f_word;
	wire	[12-1:0]	f_pkts;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	generate for(gk=0; gk<NS; gk=gk+1)
	begin : CHECK_SAXIN
		// {{{
		wire	[10:0]		fslv_word;
		wire	[12-1:0]	fslv_pkts;

		faxin_slave #(
			.DATA_WIDTH(DW)
		) faxin (
			// {{{
			.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
			//
			.S_AXIN_VALID(S_AXIN_VALID[gk]),
			.S_AXIN_READY(S_AXIN_READY[gk]),
			.S_AXIN_DATA(S_AXIN_DATA[DW * gk +: DW]),
			.S_AXIN_LAST(S_AXIN_LAST[gk]),
			.S_AXIN_ABORT(S_AXIN_ABORT[gk]),
			//
			.f_stream_word(fslv_word),
			.f_packets_rcvd(fslv_pkts)
			// }}}
		);

		always @(*)
		if (f_past_valid && !i_reset
				&& (!arb_grant[gk] || !packet_in_progress))
			assert(fslv_word == 0);
		// }}}
	end endgenerate

	faxin_master #(
		// {{{
		.DATA_WIDTH(8),
		.MIN_LENGTH(0),
		.MAX_LENGTH(0)
		// }}}
	) f_master (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		//
		.S_AXIN_VALID(M_AXIN_VALID), .S_AXIN_READY(M_AXIN_READY),
		.S_AXIN_DATA(M_AXIN_DATA), .S_AXIN_LAST(M_AXIN_LAST),
		.S_AXIN_ABORT(M_AXIN_ABORT),
		//
		.f_stream_word(f_word), .f_packets_rcvd(f_pkts)
		// }}}
	);
	// }}}

	// No *hanging* allowed
	// {{{
	always @(posedge i_clk)
	if (!i_reset && !$past(i_reset) &&
			($past(|S_AXIN_VALID) && $past(S_AXIN_READY) == 0
				&& $past(!M_AXIN_VALID || M_AXIN_READY))
			&& ($past(|S_AXIN_VALID,2)
				&& $past(S_AXIN_READY,2) == 0
				&& $past((!M_AXIN_VALID || M_AXIN_READY),2))
			&& ($past(|S_AXIN_VALID,3)
				&& $past(S_AXIN_READY,3) == 0
				&& $past((!M_AXIN_VALID || M_AXIN_READY),3))
			&& ($past(|S_AXIN_VALID,4)
				&& $past(S_AXIN_READY,4) == 0
				&& $past((!M_AXIN_VALID || M_AXIN_READY),4)) )
		assert(S_AXIN_READY != 0);
	// }}}

	generate if (DW == 8)
	begin
		always @(*)
		if (!i_reset && M_AXIN_VALID)
			assert(M_AXIN_LAST || arb_grant != 0);
	end else begin

		always @(*)
		if (!i_reset && r_valid)
			assert(r_last || arb_grant != 0);

	end endgenerate

	always @(*)
		assert($onehot0(S_AXIN_READY));

	(* anyconst *)	reg	fc_abort;

	always @(*)
	if (!fc_abort)
	begin
		assume(S_AXIN_ABORT == 0);
		assert(!r_abort);
		assert(!M_AXIN_ABORT);
	end

`endif	// FORMAL
// }}}
endmodule
