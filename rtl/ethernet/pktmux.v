////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/pktmux.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Selects from one of NUM_SRCS packet sources to send a packet
//		on the next cycle.  This core is intended to be connected
//	directly to the network transmit sink.  Sources are variable, but
//	are expected to include:
//
//		- ZipCPU,
//		- ARP replies,
//		- ICMP replies,
//		- Network debugging bus
//		- Network time
//		- Data source
//
//	Performance rule: once a source and packet have been committed, the
//	mux *MUST* complete the packet.  S_AXIN_READY will be held high,
//	therefore, from the first to the last byte.
//
//	If packets must be dropped, they will be dropped in the buffers prior
//	to this multiplexer.
//
// Status:	This module has been replaced by pktmerge, which can also handle
//		bus downsizing.
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
module	pktmux #(
		// {{{
		parameter	NUM_SRCS = 8,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		localparam	LGSRCS = $clog2(NUM_SRCS),
		localparam	NS = NUM_SRCS
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		// Incoming packets--from any number of sources
		// {{{
		input	wire	[NS-1:0]	S_AXIN_VALID,
		output	reg	[NS-1:0]	S_AXIN_READY,
		input	wire	[8*NS-1:0]	S_AXIN_DATA,
		input	wire	[NS-1:0]	S_AXIN_LAST,
		// input	wire		S_AXIN_ABORT,
		// }}}
		// Outgoing packet interface -- cannot stall
		// {{{
		output	reg		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	reg	[7:0]	M_AXIN_DATA,
		output	reg		M_AXIN_LAST
		// output reg		M_AXIN_ABORT,
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	reg	[LGSRCS-1:0]	next_index, grant_index;
	reg			access_grant;
	wire	[(1<<LGSRCS)-1:0]	s_valid, s_last;
	genvar	gk;

	generate for(gk=0; gk<NS; gk=gk+1)
	begin
		assign	{ s_last[gk], s_valid[gk] } = { S_AXIN_LAST[gk],
					S_AXIN_VALID[gk] };
	end if (NS != (1<<LGSRCS)) for(gk=NS; gk<(1<<LGSRCS); gk=gk+1)
	begin
		assign	{ s_last[gk], s_valid[gk] } = 0;
	end endgenerate
	// }}}

	// M_AXIN_VALID
	// {{{
	initial	M_AXIN_VALID = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXIN_VALID <= 0;
	else
		M_AXIN_VALID <= access_grant && s_valid[grant_index];
	// }}}

	// S_AXIN_READY
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		S_AXIN_READY <= 0;
	else if (access_grant && (|(S_AXIN_VALID & S_AXIN_READY & S_AXIN_LAST)))
		S_AXIN_READY <= 0;
	else if (!access_grant)
	begin
		S_AXIN_READY <= 0;
		S_AXIN_READY[next_index] <= s_valid[next_index]
					&& !M_AXIN_VALID && M_AXIN_READY;
	end
	// }}}

	// access_grant
	// {{{
	initial	access_grant = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		access_grant <= 0;
	else if (access_grant)
	begin
		if (|(S_AXIN_VALID & S_AXIN_READY & S_AXIN_LAST))
			access_grant <= 0;
	end else if (s_valid[next_index] && !M_AXIN_VALID && M_AXIN_READY)
		access_grant <= 1;

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert(access_grant == (|S_AXIN_READY));
`endif
	// }}}

	// next_index
	// {{{
	initial	next_index = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		next_index <= 0;
	else if ((!s_valid[next_index] && (|(S_AXIN_VALID & ~S_AXIN_READY)))
			|| (access_grant && grant_index == next_index))
	begin
		next_index <= next_index + 1;
		// Verilator lint_off WIDTH
		if (next_index >= NS-1)
			next_index <= 0;
		// Verilator lint_on  WIDTH
	end

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert(next_index < NS);
`endif
	// }}}

	// grant_index
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!access_grant)
		grant_index <= next_index;

`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && access_grant)
		assert(grant_index < NS);
`endif
	// }}}

	// M_AXIN_DATA, M_AXIN_LAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (OPT_LOWPOWER && !access_grant)
	begin
		M_AXIN_DATA <= 8'h0;
		M_AXIN_LAST <= 1'b0;
	end else if ((access_grant || !OPT_LOWPOWER)
				&& (!M_AXIN_VALID || M_AXIN_READY))
	begin
		M_AXIN_DATA <= S_AXIN_DATA[grant_index*8 +: 8];
		M_AXIN_LAST <= s_last[grant_index];
	end
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
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	// Per slave properties
	// {{{
	generate for(gk=0; gk<NS; gk=gk+1)
	begin

		// Basic AXI stream properties
		// {{{
		always @(posedge S_AXI_ACLK)
		if (!f_past_valid || $past(!S_AXI_ARESETN))
		begin
			assume(!S_AXIN_VALID[gk]);
		end else if ($past(S_AXIN_VALID[gk] && !S_AXIN_READY[gk]))
		begin
			assume(S_AXIN_VALID[gk]);
			assume($stable(S_AXIN_LAST[gk]));
			assume($stable(S_AXIN_DATA[gk*8 +: 8]));
		end
		// }}}

		// Special: Once valid goes high, it stays high for a full
		// packet
		// {{{
		always @(posedge S_AXI_ACLK)
		if (f_past_valid && $past(S_AXI_ARESETN)
				&& $past(S_AXIN_VALID[gk] && !S_AXIN_LAST[gk]))
			assume(S_AXIN_VALID[gk]);
		// }}}

		// Grant checking--only one slave can ever get access at a time
		// {{{
		// Moreover, if it has access, it must be for a valid packet
		always @(posedge S_AXI_ACLK)
		if (S_AXI_ARESETN && S_AXIN_READY[gk])
		begin
			assert(access_grant);
			assert(grant_index == gk);
			assert(S_AXIN_VALID[gk]);
		end
		// }}}

	end endgenerate
	// }}}

	// Master properties
	// {{{

	// Basic AXI stream properties
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
	begin
		assert(!M_AXIN_VALID);
	end else if ($past(M_AXIN_VALID && !M_AXIN_READY))
	begin
		assert(M_AXIN_VALID);
		assert($stable(M_AXIN_LAST));
		assert($stable(M_AXIN_DATA));
	end
	// }}}

	// Once the master channel becomes ready, it will stay that way until
	// the packet is complete
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN && M_AXIN_READY
					&& (!M_AXIN_VALID || !M_AXIN_LAST)))
		assume(M_AXIN_READY);
	// }}}

	// Once we start transmitting a packet, we will continue until it is
	// complete--no pauses allowed
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN&& M_AXIN_VALID && !M_AXIN_LAST))
		assert(M_AXIN_VALID);
	// }}}

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && M_AXIN_VALID && !M_AXIN_LAST)
	begin
		assert(access_grant);
		assert(S_AXIN_VALID[grant_index]);
	end

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && M_AXIN_VALID)
		assert(M_AXIN_READY);
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[NS-1:0]	cvr_channels, cvr_data;
	reg	[3:0]		cvr_wait;

	initial	cvr_channels = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || (!M_AXIN_VALID && M_AXIN_LAST))
		{ cvr_data, cvr_channels } <= 0;
	else begin
		cvr_channels <= cvr_channels | (S_AXIN_VALID & S_AXIN_READY & S_AXIN_LAST);
		cvr_data     <= cvr_data     | (S_AXIN_VALID & S_AXIN_READY & ~S_AXIN_LAST);
	end

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || access_grant || !S_AXIN_VALID[1])
		cvr_wait <= 0;
	else if (cvr_wait < 4'hf)
		cvr_wait <= cvr_wait + 1;

	always @(*)
	begin
		// cover(cvr_channels[0]);
		// cover(S_AXI_ARESETN && cvr_channels[0] && S_AXIN_VALID[1]);
		// cover(S_AXI_ARESETN && cvr_channels[0] && S_AXIN_VALID[1] && cvr_wait > 4'h6);
		cover(&cvr_channels[1:0]);
		cover((&cvr_channels) && (&cvr_data) && !M_AXIN_VALID);
	end
	// }}}
`endif
// }}}
endmodule
