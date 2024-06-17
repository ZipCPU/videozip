////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/pktsplitter.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Also known as the packet demux.  Takes a packet source and
//		broadcasts it to one of several potential sinks.  If a given
//	sink "matches" to the packet, packets to all other sinks will be
//	aborted.  If a sink doesn't match to the packet, the packet is aborted.
//	Similarly, if a sink drops ready mid packet, the packet will be aborted
//	as well.  (The incoming stream is not allowed to stall.)
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
`default_nettype	none
// }}}
module	pktsplitter #(
		// {{{
		parameter	NUM_SINKS = 8,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		// localparam	LGSINK = $clog2(NUM_SINKS),
		localparam	NS = NUM_SINKS
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		// Incoming packets--network source cannot stall
		// {{{
		input	wire		S_AXIN_VALID,
		output	wire		S_AXIN_READY,
		input	wire	[7:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		// }}}
		// Outgoing packet interface to each possible destination
		// {{{
		output	reg	[NS-1:0]	M_AXIN_VALID,
		input	wire	[NS-1:0]	M_AXIN_READY,
		output	reg	[8*NS-1:0]	M_AXIN_DATA,
		output	reg	[NS-1:0]	M_AXIN_LAST,
		output	reg	[NS-1:0]	M_AXIN_ABORT,
		// }}}
		// Packet sink feedback: is this packet for me or not?
		input	wire	[NS-1:0]	i_match, i_no_match
		// }}}
	);

	// Local declarations
	// {{{
	genvar	gk;
`ifdef	FORMAL
	wire	[NS-1:0]	w_mid_packet;
`endif
	// }}}

	assign	S_AXIN_READY = 1;	// Stalling the source is not allowed

	reg	s_mid_packet;

	initial	s_mid_packet = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		s_mid_packet <= 0;
	else if (S_AXIN_ABORT)
		s_mid_packet <= 0;
	else if (S_AXIN_VALID && S_AXIN_READY)
		s_mid_packet <= !S_AXIN_LAST;

	generate for(gk=0; gk<NS; gk=gk+1)
	begin
		reg	m_mid_packet;

		// M_AXIN_VALID
		// {{{
		initial	M_AXIN_VALID = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			M_AXIN_VALID[gk] <= 0;
		else if (!M_AXIN_VALID[gk] || M_AXIN_READY[gk])
		begin
			M_AXIN_VALID[gk] <= S_AXIN_VALID && !S_AXIN_ABORT
				&& (!s_mid_packet || m_mid_packet);
		end
		// }}}

		// m_mid_packet
		// {{{
		initial	m_mid_packet = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_mid_packet <= 0;
		else begin
			if (M_AXIN_VALID[gk] && M_AXIN_READY[gk] && M_AXIN_LAST[gk])
				m_mid_packet <= 0;

			if (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
			begin
				if (!M_AXIN_VALID[gk] || M_AXIN_READY[gk])
					m_mid_packet <= m_mid_packet || !s_mid_packet;
			end


			if (m_mid_packet && (!M_AXIN_VALID[gk] || !M_AXIN_READY[gk] || !M_AXIN_LAST[gk]))
			begin
				if (!i_match[gk] && (|i_match))
					m_mid_packet <= 0;

				if (i_no_match[gk])
					m_mid_packet <= 0;
			end

			// Abort on *any* stall
			if ((S_AXIN_VALID && !S_AXIN_ABORT)
				&& M_AXIN_VALID[gk] && !M_AXIN_READY[gk])
				m_mid_packet <= 0;

			// Abort if the source aborts
			if (S_AXIN_ABORT && m_mid_packet)
				m_mid_packet <= 0;
		end
		// }}}

		// M_AXIN_ABORT
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			M_AXIN_ABORT[gk] <= 0;
		else begin
			// Clear the abort once the packet is over
			if (!M_AXIN_VALID[gk] || M_AXIN_READY[gk])
			begin
				if (S_AXIN_VALID && S_AXIN_READY && S_AXIN_LAST)
					M_AXIN_ABORT[gk] <= 0;
				if (!s_mid_packet && !m_mid_packet)
					M_AXIN_ABORT[gk] <= 0;
			end

			if (m_mid_packet && (!M_AXIN_VALID[gk] || !M_AXIN_READY[gk] || !M_AXIN_LAST[gk]))
			begin
				if (!i_match[gk] && (|i_match))
					M_AXIN_ABORT[gk] <= 1;

				if (i_no_match[gk])
					M_AXIN_ABORT[gk] <= 1;
			end

			// Abort on *any* stall
			if ((S_AXIN_VALID && !S_AXIN_ABORT)
				&& M_AXIN_VALID[gk] && !M_AXIN_READY[gk])
				M_AXIN_ABORT[gk] <= 1;

			// Abort if the source aborts
			if (S_AXIN_ABORT && m_mid_packet)
				M_AXIN_ABORT[gk] <= 1;
		end
		// }}}

		// M_AXIN_DATA, M_AXIN_LAST
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!M_AXIN_VALID[gk] || M_AXIN_READY[gk])
		begin
			M_AXIN_DATA[gk*8 +: 8] <= S_AXIN_DATA;
			M_AXIN_LAST[gk]        <= S_AXIN_LAST;

			if (OPT_LOWPOWER && !S_AXIN_VALID)
			begin
				M_AXIN_DATA[gk*8 +: 8] <= 8'h0;
				M_AXIN_LAST[gk]        <= 1'b0;
			end
		end
		// }}}
`ifdef	FORMAL
		assign	w_mid_packet[gk] = m_mid_packet;
`endif
	end endgenerate

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
	localparam	LGMX = 11;
	reg			f_past_valid;
	wire	[LGMX-1:0]	s_words;

	// Reset handling
	// {{{
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);
	// }}}

	// Slave properties
	// {{{
	// Verilator lint_off PINMISSING
	faxin_slave #(
		// {{{
		.DATA_WIDTH(8),
		.MIN_LENGTH(8)
		// }}}
	) fslv (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIN_VALID(S_AXIN_VALID), .S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA), .S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		.f_stream_word(s_words)
		// }}}
	);
	// Verilator lint_on  PINMISSING

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
		assert(s_mid_packet == (s_words > 0));
	// }}}

	// Downstream matching assumptions
	// {{{
	generate for(gk=0; gk<NS; gk=gk+1)
	begin : CHECK_MATCH_ASSUMPTIONS
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!$past(M_AXIN_VALID[gk])
				|| $past(M_AXIN_READY[gk] && M_AXIN_LAST[gk]))
		begin
			// Get cleared between packets
			assume(i_match[gk] == 0);
			assume(i_no_match[gk] == 0);
		end else if ($past(i_match[gk] | i_no_match[gk]))
		begin
			assume($stable(i_match[gk]));
			assume($stable(i_no_match[gk]));
		end

		always @(*)
			assume(!i_match[gk] || !i_no_match[gk]);
		// }}}
	end endgenerate
	// }}}

	// Per master properties
	// {{{
	generate for(gk=0; gk<NS; gk=gk+1)
	begin : CHECK_PKT_MASTER
		wire	[LGMX-1:0]	m_words;

		// Verilator lint_off PINMISSING
		faxin_master #(
			// {{{
			.DATA_WIDTH(8),
			.MIN_LENGTH(8)
			// }}}
		) fmst (
			// {{{
			.S_AXI_ACLK(S_AXI_ACLK),
			.S_AXI_ARESETN(S_AXI_ARESETN),

			.S_AXIN_VALID(M_AXIN_VALID[gk]),
			.S_AXIN_READY(M_AXIN_READY[gk]),
			.S_AXIN_DATA( M_AXIN_DATA[gk*8 +: 8]),
			.S_AXIN_LAST( M_AXIN_LAST[gk]),
			.S_AXIN_ABORT(M_AXIN_ABORT[gk]),

			.f_stream_word(m_words)
			// }}}
		);
		// Verilator lint_on  PINMISSING

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN)
		begin
			if (M_AXIN_ABORT[gk])
			begin
				assert(w_mid_packet[gk] == 1'b0);
			end else if (m_words == 0 && !M_AXIN_VALID[gk])
			begin
				assert(w_mid_packet[gk] == 1'b0);
			end // else assert(w_mid_packet[gk]);
		end

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && M_AXIN_VALID[gk] && !M_AXIN_ABORT[gk])
			assert(w_mid_packet[gk]);

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN)
		begin
			if (!M_AXIN_ABORT[gk])
			begin
				if (M_AXIN_VALID[gk] && M_AXIN_LAST[gk])
				begin
					assert(s_words == 0);
				end else if (w_mid_packet[gk])
				begin
					assert(m_words + (M_AXIN_VALID[gk] ? 1:0)
							== s_words);
				end else
					assert(m_words == 0);
			end else
				assert(!w_mid_packet[gk]);
		end

		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && $past(w_mid_packet[gk] && i_no_match[gk]
				&& (!M_AXIN_VALID[gk] || !M_AXIN_READY[gk] || !M_AXIN_LAST[gk])))
			assert(!w_mid_packet[gk]);


		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && $past(w_mid_packet[gk] && !i_match[gk])
				&& $past(M_AXIN_VALID[gk] && !M_AXIN_LAST[gk] && !M_AXIN_ABORT[gk])
				&& $past(|i_match))
			assert(!M_AXIN_VALID[gk] || M_AXIN_ABORT[gk]);

		always @(*)
		if (S_AXI_ARESETN && !s_mid_packet)
			assert(!w_mid_packet[gk] || (M_AXIN_VALID[gk] && M_AXIN_LAST[gk]));

	end endgenerate

	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks (not yet implemented)
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Careless assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
