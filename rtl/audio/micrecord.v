////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/audio/micrecord.v
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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
module	micrecord #(
		// {{{
		parameter	[15:0]	UDP_DATAPORT = 8546,
		localparam		LGAUDIO = 8,
		localparam		SAMPLES_PER_PACKET = (1<<LGAUDIO)/2
		// }}}
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		//
		input	wire		i_en,
		input	wire	[63:0]	i_timestamp,
		input	wire	[1:0]	i_cfg_wet_id,
		//
		input	wire	[47:0]	i_enet_dest,
		input	wire	[31:0]	i_my_ipaddr,
		input	wire	[31:0]	i_ip_dest,
		//
		//
		input	wire		S_MIC_TVALID,
		output	wire		S_MIC_TREADY,
		input	wire	[23:0]	S_MIC_TDATA,
		input	wire		S_MIC_TLAST,
		//
		output	wire		M_UDP_VALID,
		input	wire		M_UDP_READY,
		output	wire	[31:0]	M_UDP_DATA,
		output	wire		M_UDP_LAST,
		//
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	P_IDLE        = 2'b00,
				// P_CONFIG      = 2'b00,
				P_TIMESTAMPHI = 2'b01,
				P_TIMESTAMPLO = 2'b10,
				P_PAYLOAD     = 2'b11;

	wire		start_frame;
	wire	[31:0]	cfg_data;

	reg	[1:0]	pkt_state;
	reg		pkt_valid, pkt_last, pkt_abort, pkt_syncd;
	wire		pkt_ready;
	reg	[31:0]	pkt_data;

	reg	[63:0]	r_timestamp;
	reg	[9:0]	frame_count;
	reg	[4:0]	abort_count;
	reg	[9:0]	drop_count;

	reg		last_stall, dropped_data;
	reg	[24:0]	last_data;

	reg	[LGAUDIO-2:0]	sample_count;
	wire	[31:0]	udp_debug;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skid FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	wire		skd_valid, skd_ready, skd_last;
	wire	[23:0]	skd_data;

`ifdef	FORMAL
	localparam	SKDLGLEN = 0;
`else
	localparam	SKDLGLEN = 4;
`endif

	generate if (SKDLGLEN > 1)
	begin : GEN_SKDFIFO
		wire		skd_full, skd_empty;
		wire	[SKDLGLEN:0]	skd_fill;

		sfifo #(
			.BW(25), .LGFLEN(SKDLGLEN)
		) skdfifo (
			// {{{
			.i_clk(S_AXI_ACLK),
			.i_reset(!S_AXI_ARESETN || dropped_data),
			.i_wr(S_MIC_TVALID), .i_data({S_MIC_TLAST, S_MIC_TDATA}),
				.o_full(skd_full), .o_fill(skd_fill),
			.i_rd(skd_ready),
				.o_data({skd_last, skd_data}),
				.o_empty(skd_empty)
			// }}}
		);

		assign	skd_valid = !skd_empty;
		assign	S_MIC_TREADY = !skd_full;

		// Verilator lint_off UNUSED
		wire	unused_skdfifo;
		assign	unused_skdfifo = &{ 1'b0, skd_fill };
		// Verilator lint_on  UNUSED
	end else begin : NO_SKDFIFO

		assign	skd_valid = S_MIC_TVALID;
		assign	skd_data  = S_MIC_TDATA;
		assign	skd_last  = S_MIC_TLAST;
		assign	S_MIC_TREADY = skd_ready;

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packet generation
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	skd_ready = (pkt_state == P_IDLE && (!i_en || !pkt_syncd))
			||(pkt_state == P_PAYLOAD && (!pkt_valid || pkt_ready));

	assign	start_frame = (!pkt_valid || pkt_ready) && pkt_state == P_IDLE
			&& pkt_syncd && i_en;

	// pkt_syncd
	// {{{
	initial	pkt_syncd = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pkt_syncd <= 1;
	else if (skd_valid && skd_ready)
		pkt_syncd <= skd_last;
	// }}}

	// r_timestamp
	// {{{
	always @(posedge S_AXI_ACLK)
	if (start_frame)
		r_timestamp <= i_timestamp;
	// }}}

	// frame_count
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		frame_count <= 0;
	else if (start_frame)
		frame_count <= frame_count + 1;
	// }}}

	// abort_count
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		abort_count <= 0;
	else if (!pkt_abort && (pkt_state != P_IDLE)&& dropped_data)
		abort_count <= abort_count + 1;
	// }}}

	// drop_count
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		drop_count <= 0;
	else if (last_stall && (!S_MIC_TVALID
				|| ({ S_MIC_TDATA, S_MIC_TLAST } != last_data)))
		drop_count <= drop_count + 1;
	// }}}

	// last_stall, last_data, dropped_data detection
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		last_stall <= 0;
		dropped_data <= 0;
	end else begin
		last_stall <= S_MIC_TVALID && !S_MIC_TREADY;

		if (start_frame)
			dropped_data <= 0;
		if (!dropped_data && last_stall)
			dropped_data <= !S_MIC_TVALID
				|| ({ S_MIC_TDATA, S_MIC_TLAST } != last_data);
	end
	// }}}

	always @(posedge S_AXI_ACLK)
		last_data  <= { S_MIC_TDATA, S_MIC_TLAST };

	assign	cfg_data = { 4'b1000, frame_count[9:0], i_cfg_wet_id,
				dropped_data, abort_count[4:0], drop_count };

	initial	pkt_state    = P_IDLE;
	initial	pkt_valid    = 1'b0;
	initial	pkt_data     = 0;
	initial	pkt_last     = 1'b0;
	initial	pkt_abort    = 1'b0;
	initial	sample_count = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		pkt_state <= P_IDLE;
		pkt_valid <= 0;
		pkt_data  <= 0;
		pkt_last  <= 0;
		pkt_abort <= 0;
		sample_count <= 0;
		// }}}
	end else begin
		if (pkt_ready)
			pkt_valid <= 0;

		if (pkt_ready)
		begin
			pkt_abort <= 0;
			pkt_data <= 0;
			pkt_last <= 0;
		end

		if ((pkt_state != P_IDLE)&&(dropped_data || !i_en))
			pkt_abort <= 1;

		if (!pkt_valid || pkt_ready) case(pkt_state)
		P_IDLE: begin
			// {{{
			sample_count <= 0;
			pkt_data <= cfg_data;
			if (start_frame)
			begin
				pkt_valid <= 1'b1;
				pkt_state <= P_TIMESTAMPHI;
			end end
			// }}}
		P_TIMESTAMPHI: begin
			// {{{
			sample_count <= 0;
			pkt_valid <= 1'b1;
			pkt_data <= r_timestamp[63:32];
			pkt_state <= P_TIMESTAMPLO;
			end
			// }}}
		P_TIMESTAMPLO: begin
			// {{{
			sample_count <= 0;
			pkt_valid <= 1'b1;
			pkt_data <= r_timestamp[31:0];
			pkt_state <= P_PAYLOAD;
			end
			// }}}
		P_PAYLOAD: begin
			// {{{
			pkt_valid <= skd_valid;
			pkt_data <= { 8'h00, skd_data };
			pkt_state <= P_PAYLOAD;

			if (skd_valid && skd_last)
				sample_count <= sample_count + 1;

			if (skd_valid && skd_last
				&& sample_count + 1 >= SAMPLES_PER_PACKET)
			begin
				pkt_last  <= 1'b1;
				pkt_state <= P_IDLE;
			end end
			// }}}
		default: begin
			pkt_state <= P_IDLE;
			end
		endcase

		if (pkt_abort && (!pkt_valid || pkt_ready))
		begin
			pkt_valid <= 0;
			pkt_state <= P_IDLE;
			pkt_last  <= 0;
		end

		if (pkt_abort)
			sample_count <= 0;
	end
	// }}}
`ifndef	FORMAL
	////////////////////////////////////////////////////////////////////////
	//
	// Generate an IP header for our UDP packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	wire		IPHDR_VALID, IPHDR_READY, IPHDR_LAST;
	wire	[31:0]	IPHDR_DATA;

	ipheader
	u_ip (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.i_enet_dest(i_enet_dest),
		.i_ip_src(   i_my_ipaddr),
		.i_ip_dest(  i_ip_dest),
		//
		.M_AXI_TVALID(IPHDR_VALID),
		.M_AXI_TREADY(IPHDR_READY),
		.M_AXI_TDATA( IPHDR_DATA),
		.M_AXI_TLAST( IPHDR_LAST)
		// }}}
	);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Turn the inputs into an IP packet
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	pkt2udp #(
		.LGMEM(LGAUDIO+1)
	) u_udp (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.i_udp_sport(UDP_DATAPORT), .i_udp_dport(UDP_DATAPORT),
		//
		.S_AXIN_VALID(pkt_valid),
		.S_AXIN_READY(pkt_ready),
		.S_AXIN_DATA( pkt_data),
		.S_AXIN_LAST( pkt_last),
		.S_AXIN_ABORT(pkt_abort),
		//
		.S_HDR_VALID(IPHDR_VALID),
		.S_HDR_READY(IPHDR_READY),
		.S_HDR_DATA( IPHDR_DATA),
		.S_HDR_LAST( IPHDR_LAST),
		//
		.M_AXIS_VALID(M_UDP_VALID),
		.M_AXIS_READY(M_UDP_READY),
		.M_AXIS_DATA( M_UDP_DATA),
		.M_AXIS_LAST( M_UDP_LAST),
		//
		.o_debug(udp_debug)
		// }}}
	);

	/*
	wire	smoke;

	udpsmokedet 
	u_smoke (
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIN_VALID(M_UDP_VALID),
		.S_AXIN_READY(M_UDP_READY),
		.S_AXIN_DATA(M_UDP_DATA),
		.o_smoke(smoke)
	);

	assign	o_debug = { smoke, udp_debug[30:0] };
	*/

	assign	o_debug = { 1'b0, udp_debug[30:0] };
	// }}}
`endif

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, udp_debug };
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
	(* anyconst *)	reg		f_nvr_drop, fnvr_check;
	(* anyconst *)	reg [23:0]	fnvr_sample;

	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming AXI stream assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assume(!S_MIC_TVALID);
	else if (f_nvr_drop && $past(S_MIC_TVALID && !S_MIC_TREADY))
	begin
		assume(S_MIC_TVALID);
		assume($stable(S_MIC_TDATA));
		assume($stable(S_MIC_TLAST));
	end

	always @(*)
	if (S_MIC_TVALID)
		assume(S_MIC_TLAST == !pkt_syncd);

	always @(*)
	if (S_AXI_ARESETN && f_nvr_drop)
		assert(!dropped_data);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing AXI network properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	localparam	F_PKTLEN = 3 + (SAMPLES_PER_PACKET * 2);
	localparam	F_LGPKT = $clog2(F_PKTLEN+1);
	wire	[F_LGPKT-1:0]	faxin_word;
	wire	[11:0]		faxin_packets;

	faxin_master #(
		// {{{
		.DATA_WIDTH(32),
		.MIN_LENGTH(F_PKTLEN),
		.MAX_LENGTH(F_PKTLEN)
		// }}}
	) faxin (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIN_VALID(pkt_valid),
		.S_AXIN_READY(pkt_ready),
		.S_AXIN_DATA( pkt_data),
		.S_AXIN_LAST( pkt_last),
		.S_AXIN_ABORT(pkt_abort),
		//
		.f_stream_word(faxin_word),
		.f_packets_rcvd(faxin_packets)
		// }}}
	);

	always @(*)
	if (S_AXI_ARESETN && pkt_valid && pkt_last)
		assert(sample_count == 0);

	always @(*)
	if (S_AXI_ARESETN && !pkt_abort)
	case(pkt_state)
	P_IDLE: begin
		assert(sample_count == 0);
		if (!pkt_valid)
		begin
			assert(!pkt_last);
			assert(faxin_word == 0);
		end else if (pkt_valid)
		begin
			assert(pkt_last);
			assert(faxin_word == (SAMPLES_PER_PACKET * 2)+2);
		end end
	P_TIMESTAMPHI: begin
		assert(pkt_valid && faxin_word == 0);
		assert(pkt_syncd);
		assert(!pkt_last);
		assert(sample_count == 0);
		end
	P_TIMESTAMPLO: begin
		assert(pkt_valid && faxin_word == 1);
		assert(pkt_syncd);
		assert(!pkt_last);
		assert(sample_count == 0);
		end
	P_PAYLOAD:     begin
		assert(faxin_word + (pkt_valid ? 1:0) >= 3);
		assert(!pkt_last);
		if (faxin_word + (pkt_valid ? 1:0) == 3)
		begin
			assert(sample_count == 0 && pkt_syncd);
		end else begin
			assert(faxin_word + (pkt_valid ? 1:0)
				== 3+({1'b0, sample_count, 1'b0 }) + (pkt_syncd ? 0:1));
		end end
	endcase

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Never data checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (S_MIC_TVALID)
		assume(S_MIC_TDATA != fnvr_sample);

	always @(*)
	if (pkt_valid && pkt_state == P_PAYLOAD && faxin_word > 2)
		assert(pkt_data != { 8'h0, fnvr_sample });

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// }}}
`endif
// }}}
endmodule
