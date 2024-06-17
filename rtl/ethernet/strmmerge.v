////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/strmmerge.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Given NS packet sources, this stream merger merges all of the
//		packet sources into a single destination packet stream.  Two
//	assumptions are made of the inputs: 1) Incoming packets are assumed to
//	begin with the number of bytes in the packet as their first word.
//	(This is to allow them to be stored into memory, where the last pointer
//	would otherwise be low.)  2) Incoming data streams are assumed to be
//	able to handle an arbitrary amount of backpressure if necessary.
//	(The pktmerge module can deal with packets that will ABORT under
//	backpressure, and that have LAST set properly.)
//
//	This module works by first generating the LAST property for each
//	stream, and then uses that to help arbitrate packets together.
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
module	strmmerge #(
		// {{{
		parameter	NS = 4,
		parameter	DW = 32,
		localparam [0:0]	OPT_LOWPOWER = 1'b0
		// }}}
	) (
		// {{{
		input	wire			S_AXI_ACLK,
		// Verilator lint_off SYNCASYNCNET
		input	wire			S_AXI_ARESETN,
		// Verilator lint_on  SYNCASYNCNET
		//
		input	wire	[NS-1:0]	S_AXIS_TVALID,
		output	wire	[NS-1:0]	S_AXIS_TREADY,
		input	wire	[DW*NS-1:0]	S_AXIS_TDATA,
		//
		output	wire			M_AXIS_TVALID,
		input	wire			M_AXIS_TREADY,
		output	wire	[DW-1:0]	M_AXIS_TDATA,
		output	wire			M_AXIS_TLAST
		// }}}
	);

	// Local declarations
	// {{{
	genvar	gk;
	wire	[NS-1:0]	S_AXIS_TLAST;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet arbitration
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire	[NS-1:0]	grant;

	generate if (NS == 1)
	begin : NO_ARBITRATION

		assign	grant = 1;
		assign	S_AXIS_TREADY = M_AXIS_TREADY;

	end else begin : GEN_ARBITRATION
		reg			arb_stalled;

		pktarbiter #(
			.W(NS)
		) u_arbiter (
			// {{{
			.i_clk(S_AXI_ACLK), .i_reset_n(S_AXI_ARESETN),
			//
			.i_req(S_AXIS_TVALID), .i_stall(arb_stalled),
			.o_grant(grant)
			// }}}
		);

		initial	arb_stalled = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			arb_stalled <= 0;
		else if (|S_AXIS_TVALID)
		begin
			arb_stalled <= 1;
			if (|(S_AXIS_TVALID & S_AXIS_TREADY & S_AXIS_TLAST))
				arb_stalled <= 0;
		end

		assign	S_AXIS_TREADY = (arb_stalled && (!M_AXIS_TVALID || M_AXIS_TREADY)) ? grant : 0;

`ifdef	FORMAL
		always @(*)
		if (S_AXI_ARESETN && grant == 0)
			assert(!arb_stalled);
		always @(*)
		if (S_AXI_ARESETN && M_AXIS_TVALID && !M_AXIS_TLAST)
			assert(grant != 0);
`endif
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Last generation from the packet length word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam	CW = 16 - $clog2(DW/8);
`ifdef	FORMAL
	wire	[CW*NS-1:0]	s_count_vector;
`endif

	generate for(gk=0; gk<NS; gk=gk+1)
	begin : GEN_SLAST
		// {{{
		reg			last;
		reg	[CW-1:0]	count;
		wire	[15:0]		rounded_up;
		wire	[16-1:0]	w_data;

		assign	w_data = S_AXIS_TDATA[gk*DW +: 16];

		assign	rounded_up = w_data - (DW/8)
			+ { {(16-$clog2(DW/8)){1'b0}}, {($clog2(DW/8)){1'b1}} };

		initial	count = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			count <= 0;
		else if (S_AXIS_TVALID[gk] && S_AXIS_TREADY[gk])
		begin
			if (count > 0)
				count <= count - 1;
			else // if (count == 0)
				count <= rounded_up[15:$clog2(DW/8)];
		end

		initial	last = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			last <= 0;
		else if (S_AXIS_TVALID[gk] && S_AXIS_TREADY[gk])
		begin
			last <= (count == 2);
			if (count == 0)
				last <= (rounded_up[15:$clog2(DW/8)] == 1);
		end

		assign	S_AXIS_TLAST[gk] = last;

		// Verilator lint_off UNUSED
		wire	unused_slast;
		assign	unused_slast = &{ 1'b0, rounded_up[1:0] };
		// Verilator lint_on  UNUSED
`ifdef	FORMAL
		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || $past(!S_AXI_ARESETN))
			assume(!S_AXIS_TVALID[gk]);
		else if ($past(S_AXIS_TVALID[gk] && !S_AXIS_TREADY[gk]))
		begin
			assume(S_AXIS_TVALID[gk]);
			assume($stable(S_AXIS_TDATA[gk*DW +: DW]));
			assert($stable(S_AXIS_TLAST[gk]));
		end

		always @(*)
		if (S_AXI_ARESETN && S_AXIS_TVALID[gk] && count == 0)
			assume(S_AXIS_TDATA[gk*DW +: 16] > (DW/8));

		always @(*)
		if (S_AXI_ARESETN)
			assert(last == (count == 1));

		assign	s_count_vector[gk * CW +: CW] = count;

		always @(*)
		if (S_AXI_ARESETN && count > 0)
			assert(grant[gk]);
`endif
		// }}}
	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Last generation from the packet length word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate if (NS == 1)
	begin : MERGE_SINGLE_SLAVE

		assign	M_AXIS_TVALID = S_AXIS_TVALID[0];
		assign	M_AXIS_TDATA  = S_AXIS_TDATA;
		assign	M_AXIS_TLAST  = S_AXIS_TLAST[0];

	end else begin : GEN_MERGE
		integer			ik;
		reg	[DW-1:0]	next_data, m_data;
		reg			next_last, m_valid, m_last;

		// next_data, next_last
		// {{{
		always @(*)
		begin
			next_data = 0;
			for(ik=0; ik<NS; ik=ik+1)
			if ((grant[ik]&& !OPT_LOWPOWER)
				|| (OPT_LOWPOWER &&S_AXIS_TVALID[ik] && S_AXIS_TREADY[ik]))
				next_data = next_data | S_AXIS_TDATA[DW*ik+: DW];

			next_last = 0;
			next_last = |(S_AXIS_TLAST & grant);
		end
		// }}}

		// M_AXIS_TVALID
		// {{{
		initial	m_valid = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			m_valid <= 0;
		else if (!M_AXIS_TVALID || M_AXIS_TREADY)
			m_valid <= |(S_AXIS_TVALID & S_AXIS_TREADY);
		// }}}

		// M_AXIS_TDATA, M_AXIS_TLAST
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!M_AXIS_TVALID || M_AXIS_TREADY)
		begin
			m_data <= next_data;
			m_last <= next_last;
		end
		// }}}

		assign	M_AXIS_TVALID = m_valid;
		assign	M_AXIS_TDATA  = m_data;
		assign	M_AXIS_TLAST  = m_last;
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
	reg		f_past_valid;
	reg	[15:0]	m_words;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!M_AXIS_TVALID);
	else if ($past(M_AXIS_TVALID && !M_AXIS_TREADY))
	begin
		assert(M_AXIS_TVALID);
		assert($stable(M_AXIS_TDATA));
		assert($stable(M_AXIS_TLAST));
	end

	initial	m_words = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_words <= 0;
	else if (M_AXIS_TVALID && M_AXIS_TREADY)
	begin
		m_words <= m_words + 1;
		if (M_AXIS_TLAST)
			m_words <= 0;
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN)
	begin
		if (m_words > 0)
			assert(M_AXIS_TLAST || grant != 0);
	end

	// Correlate m_words with the currently active slave
	// {{{
	generate for(gk=0; gk<NS; gk=gk+1)
	begin : SLV_WORD_COUNT
		reg[15:0]	s_words;
		wire	[CW-1:0]	s_count;

		initial	s_words = 0;
		always @(posedge S_AXI_ACLK)
		if (!S_AXI_ARESETN)
			s_words <= 0;
		else if (S_AXIS_TVALID[gk] && S_AXIS_TREADY[gk])
		begin
			s_words <= s_words + 1;
			if (S_AXIS_TLAST[gk])
				s_words <= 0;
		end

		assign	s_count = s_count_vector[gk * CW +: CW];

		always @(*)
		if (S_AXI_ARESETN)
		begin
			if (M_AXIS_TLAST || !grant[gk])
				assert(s_words == 0);
			else
				assert(s_words==(M_AXIS_TVALID ? 1:0) + m_words);

			if (s_count == 0)
				assert(s_words == 0);
			else
				assert(grant[gk]);

			assert(s_count < (32'h1<<CW));
			assert(s_count + s_words <= (32'h1<<CW));
		end
	end endgenerate
	// }}}
`endif
// }}}
endmodule
