////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/audio/audiomux.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Select between a number of audio sources (streams).
//
// Two register:
//	0, Bits 20-16	Selects the LEFT  channel
//	0, Bits  4- 0	Selects the RIGHT channel
//	1:		Tracking the RX speed
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
`default_nettype none
// }}}
module	audiomux #(
		// {{{
		parameter	NS = 3,	// Number of incoming audio streams
		parameter	RXW = 24,	// Width of audio data
		parameter	DW = 32,
		parameter	ADC_PFIL_NCOEFFS = 20,
		parameter	TX_PFIL_NCOEFFS = 83,
		parameter [0:0]	OPT_TEST_SOURCE = 1'b0
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset, i_pps,
		//
		// Wishbone slave inputs
		// {{{
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		// Single address only
		input	wire	[3:0]		i_wb_addr,
		input	wire	[DW-1:0]	i_wb_data,
		input	wire	[DW/8-1:0]	i_wb_sel,
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[DW-1:0]	o_wb_data,
		// }}}
		// Incoming data sets
		// {{{
		// Incoming RX data
		input	wire			rx_stb,
		input	wire	[NS*RXW-1:0]	raw_rx_data,
		// Incoming TX data
		input	wire	[1:0]		raw_tx_data,
		// Incoming MIC data
		input	wire			S_MIC_TVALID,
		output	wire			S_MIC_TREADY,
		input	wire	[RXW-1:0]	S_MIC_TDATA,
		input	wire			S_MIC_TLAST,
		// Incoming TEST data
		input	wire			S_TEST_TVALID,
		output	wire			S_TEST_TREADY,
		input	wire	[RXW-1:0]	S_TEST_TDATA,
		// }}}
		// Outgoing audio data
		// {{{
		output	reg			M_AUD_TVALID,
		input	wire			M_AUD_TREADY,
		output	reg	[RXW-1:0]	M_AUD_TDATA,
		output	reg			M_AUD_TLAST,
		// }}}
		output	reg	[31:0]		o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	PFIL_TW = 16;
	localparam [3:0]	ADR_SELECT  = 4'h0,
				ADR_TXRATE  = 4'h7,
				ADR_ADCRATE = 4'h8,
				ADR_TXFIL   = 4'h9,
				ADR_ADCFIL  = 4'ha,
				ADR_RSCONFIG= 4'hb;

	integer		ik;

	reg	[4:0]	left_sel, right_sel;
	reg	[27:0]	partial_mic_count, mic_sample_rate;
	reg	[31:0]	partial_adc_count, adc_sample_rate;
	reg	[27:0]	partial_out_count, out_sample_rate;
	reg	[27:0]	left_count,  left_rate;
	reg	[27:0]	right_count, right_rate;
	reg	[31:0]	pps_count;

	wire	[1:0]	long_tx_data;
	reg	[1:0]	tx_val;

	reg	[RXW-1:0]	raw_rx_left, raw_rx_right;

	wire		tx_cic_stb, ign_tx_cic_ready;
	wire	[8:0]	tx_cic_data;

	reg	[1:0]	tx_sw;
	reg	[31:0]	tx_resample_rate;
	wire		tx_resample_valid, tx_resample_ready;
	wire	[RXW-1:0]	tx_resample_data;

	reg	[1:0]	adc_sw;
	reg	[31:0]	adc_resample_rate;

	wire		left_adc_cic_stb, ign_left_adc_cic_ready;
	wire	[RXW-1:0]	left_adc_cic_data;

	wire		right_adc_cic_stb, ign_right_adc_cic_ready;
	wire	[RXW-1:0]	right_adc_cic_data;

	wire		adc_left_valid, adc_left_ready;
	wire	[RXW-1:0]	adc_left_data;

	wire		adc_right_valid, adc_right_ready;
	wire	[RXW-1:0]	adc_right_data;

	reg	[RXW-1:0]	left_value, right_value, out_left, out_right;

	// }}}

	assign	S_MIC_TREADY = 1'b1;
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone handling
	// {{{

	// Registers:
	//	 0: Selection, 16'bUNUSED, 8'bLEFT, 8'bRIGHT
	//	 1: Samples per second MIC input	(Feedback)
	//	 2: Samples per second ADC input	(Feedback)
	//	 3: Samples per second output	(Feedback)
	//
	//	 4: Samples per second out of TX resampler
	//	 5: Samples per second out of left  ADC resampler
	//	 6: Samples per second out of right ADC resampler
	//	 7: TX resampler rate
	//	 8: ADC resampler rate
	//	 9: TX resampler filter (write only)
	//	10: ADC resampler filter (write only)
	//	11: Resampler config
	//	12: PPS count
	//	13:
	//	14:
	//	15:

	// mic_sample_rate
	// {{{
	always @(posedge i_clk)
	if (i_pps)
	begin
		partial_mic_count <= (S_MIC_TVALID && S_MIC_TREADY && S_MIC_TLAST) ? 1:0;
		mic_sample_rate <= partial_mic_count;
	end else if (S_MIC_TVALID && S_MIC_TREADY && S_MIC_TLAST)
		partial_mic_count <= partial_mic_count + 1;
	// }}}

	// adc_sample_rate
	// {{{
	always @(posedge i_clk)
	if (i_pps)
	begin
		partial_adc_count <= rx_stb ? 1:0;
		adc_sample_rate <= partial_adc_count;
	end else if (rx_stb)
		partial_adc_count <= partial_adc_count + 1;
	// }}}

	// out_sample_rate
	// {{{
	always @(posedge i_clk)
	if (i_pps)
	begin
		partial_out_count <= (M_AUD_TVALID && M_AUD_TREADY && M_AUD_TLAST) ? 1:0;
		out_sample_rate <= partial_out_count;
	end else if (M_AUD_TVALID && M_AUD_TREADY && M_AUD_TLAST)
		partial_out_count <= partial_out_count + 1;
	// }}}

	assign	o_wb_stall = 1'b0;

	// left_sel, right_sel
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		// Default to TX ch (left) and RX chan #0 (right)
		{ left_sel, right_sel } <= { 5'h1f, 5'd22 };

		// Unless we have a test source installed.  In that case,
		// default the right channel to the test source
		if (OPT_TEST_SOURCE)
			right_sel <= 5'd22; // Default to test tone
	end else if (i_wb_stb && i_wb_we && i_wb_addr == ADR_SELECT)
	begin
		if (i_wb_sel[1])
			left_sel <= i_wb_data[12:8];
		if (i_wb_sel[0])
			right_sel <= i_wb_data[4:0];
	end
	// }}}

	// tx_resample_rate
	// {{{
	// RSLT = Incoming rate * (CIC IN / CIC DOWN) * (resample_rate) / 2^32
	//	= 96kHz
	// resample_rate = 96e3 / 100e6 * (512 / 1) * 2^32
	//
	// localparam [31:0]	DEF_TX_RESAMPLE_RATE = 32'h7dd4_4135;
	// localparam [31:0]	DEF_TX_RESAMPLE_RATE = 32'h3eea_209a;
	// localparam [31:0]	DEF_TX_RESAMPLE_RATE = 32'hfba8_826a;
	// localparam [31:0]	DEF_TX_RESAMPLE_RATE = 32'h0fba_8827;
	localparam [31:0]	DEF_TX_RESAMPLE_RATE = 32'h07dd_4413;
	initial	tx_resample_rate = DEF_TX_RESAMPLE_RATE;
	always @(posedge i_clk)
	if (i_reset)
		tx_resample_rate <= DEF_TX_RESAMPLE_RATE;
	else if (i_wb_stb && i_wb_we && i_wb_addr == ADR_TXRATE)
	begin
		if (i_wb_sel[3])
			tx_resample_rate[31:24] <= i_wb_data[31:24];
		if (i_wb_sel[2])
			tx_resample_rate[23:16] <= i_wb_data[23:16];
		if (i_wb_sel[1])
			tx_resample_rate[15: 8] <= i_wb_data[15: 8];
		if (i_wb_sel[0])
			tx_resample_rate[ 7: 0] <= i_wb_data[ 7: 0];
	end
	// }}}

	// adc_resample_rate
	// {{{
	// RSLT = Incoming rate * (CIC IN / CIC DOWN) * (resample_rate) / 2^32
	//	= 96kHz
	// resample_rate = 96e3 / 1.2e6 * (4 / 1) * 2^32
	// localparam [31:0]	DEF_ADC_RESAMPLE_RATE = 32'h51eb_851f;
	localparam [31:0]	DEF_ADC_RESAMPLE_RATE = 32'h28f5_c28f;

	initial	adc_resample_rate = DEF_ADC_RESAMPLE_RATE;
	always @(posedge i_clk)
	if (i_reset)
		adc_resample_rate <= DEF_ADC_RESAMPLE_RATE;
	else if (i_wb_stb && i_wb_we && i_wb_addr == ADR_ADCRATE)
	begin
		if (i_wb_sel[3])
			adc_resample_rate[31:24] <= i_wb_data[31:24];
		if (i_wb_sel[2])
			adc_resample_rate[23:16] <= i_wb_data[23:16];
		if (i_wb_sel[1])
			adc_resample_rate[15: 8] <= i_wb_data[15: 8];
		if (i_wb_sel[0])
			adc_resample_rate[ 7: 0] <= i_wb_data[ 7: 0];
	end
	// }}}

	// tx_sw, adc_sw
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		tx_sw <= 2'b10;
		adc_sw <= 2'b10;
	end else if (i_wb_stb && i_wb_we && i_wb_addr == ADR_RSCONFIG)
	begin
		if (i_wb_sel[0])
			tx_sw <= i_wb_data[1:0];
		if (i_wb_sel[1])
			adc_sw <= i_wb_data[9:8];
	end
	// }}}

	// pps_count
	// {{{
	initial	pps_count = 0;
	always @(posedge i_clk)
	if (i_reset)
		pps_count <= 0;
	else if (i_pps)
		pps_count <= pps_count + 1;
	// }}}

	// o_wb_ack
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		o_wb_ack <= 0;
	else
		o_wb_ack <= i_wb_stb;
	// }}}

	// o_wb_data
	// {{{
	always @(posedge i_clk)
	begin
		o_wb_data <= 0;

		case(i_wb_addr)
		4'h0: o_wb_data[15:0] <= { 3'h0, left_sel, 3'h0, right_sel };
		4'h1: o_wb_data[27:0] <= mic_sample_rate;
		4'h2: o_wb_data[31:0] <= adc_sample_rate;
		4'h3: o_wb_data[27:0] <= out_sample_rate;
		4'h7: o_wb_data <= tx_resample_rate;
		4'h8: o_wb_data <= adc_resample_rate;
		4'hb: o_wb_data <= { 16'h0, 6'h0, adc_sw, 6'h0, tx_sw };
		4'hc: o_wb_data <= pps_count;
		4'hd: o_wb_data[27:0] <=  left_rate;
		4'he: o_wb_data[27:0] <= right_rate;
		default: begin end
		endcase

		if (!i_wb_stb || i_wb_we)
			o_wb_data <= 0;
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// TX input goes directly into a CIC based downsampler
	// {{{

	tx_pulswidth #(
		.LGAMP(17)
	) widen_tx_pulse (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset), .i_ce(1'b1),
		.i_amp({(17){1'b1}}), .i_data(raw_tx_data),
		.o_data(long_tx_data)
		// }}}
	);

	always @(*)
	begin
		casez(long_tx_data)
		2'b00: tx_val = 2'b00;
		2'b1?: tx_val = 2'b11;
		2'b01: tx_val = 2'b01;
		endcase
	end

	asrc_cicdown #(
		.IW(2), .OW(9), .LGMEM(10), .SHIFT(16)
	) u_txcic (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_navg(64), .i_ce(1'b1), .i_val(tx_val),
		.o_ce(tx_cic_stb), .o_val(tx_cic_data)
		// }}}
	);

	// And into the asynchronous resampler
	// {{{
	asrc_main #(
		.IW(9), .OW(RXW), .PFIL_TW(PFIL_TW),
		.PFIL_NCOEFFS(TX_PFIL_NCOEFFS)
	) u_tx_resampler (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Configuration
		// {{{
		.i_up_switch(1'b0),
		.i_cic_switch(1'b0), .i_pfil_switch(tx_sw[0]),
		.i_poly_switch(tx_sw[1]),
		.i_prefil_write(i_wb_stb && i_wb_we && i_wb_addr == ADR_TXFIL),
		.i_prefil_tap(i_wb_data[31:32-PFIL_TW]),
		//
		.i_resample_rate(tx_resample_rate),
		// }}}
		.S_AXIS_TVALID(tx_cic_stb),
			.S_AXIS_TREADY(ign_tx_cic_ready),
			.S_AXIS_TDATA(tx_cic_data),
		//
		.M_AXIS_TVALID(tx_resample_valid),
			.M_AXIS_TREADY(tx_resample_ready),
			.M_AXIS_TDATA(tx_resample_data)
		// }}}
	);

	assign	tx_resample_ready = 1'b1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RX left -- select an ADC channel for the CIC downsampler
	// {{{

	// raw_rx_left
	// {{{
	always @(posedge i_clk)
	if (rx_stb)
	begin
		raw_rx_left <= raw_rx_data[RXW-1:0];
		for(ik=0; ik<NS; ik=ik+1)
		if (ik[4:0] == left_sel)
			raw_rx_left <= raw_rx_data[RXW*ik +: RXW];
	end
	// }}}

	// Left CIC
	// {{{
	asrc_cicdown #(
		.IW(RXW), .OW(RXW), .LGMEM(5), .SHIFT(11)
	) u_left_adc_cic (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_navg(4), .i_ce(rx_stb), .i_val(raw_rx_left),
		.o_ce(left_adc_cic_stb), .o_val(left_adc_cic_data)
		// }}}
	);
	// }}}

	// Left asynchronous resampler
	// {{{
	asrc_main #(
		.IW(RXW), .OW(RXW), .PFIL_TW(PFIL_TW),
		.PFIL_NCOEFFS(ADC_PFIL_NCOEFFS)
	) u_left_resampler (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Configuration
		// {{{
		.i_up_switch(1'b0),
		.i_cic_switch(1'b0), .i_pfil_switch(adc_sw[0]),
		.i_poly_switch(adc_sw[1]),
		.i_prefil_write(i_wb_stb && i_wb_we && i_wb_addr == ADR_ADCFIL),
		.i_prefil_tap(i_wb_data[31:32-PFIL_TW]),
		//
		.i_resample_rate(adc_resample_rate),
		// }}}
		.S_AXIS_TVALID(left_adc_cic_stb),
			.S_AXIS_TREADY(ign_left_adc_cic_ready),
			.S_AXIS_TDATA(left_adc_cic_data),
		//
		.M_AXIS_TVALID(adc_left_valid),
			.M_AXIS_TREADY(adc_left_ready),
			.M_AXIS_TDATA(adc_left_data)
		// }}}
	);

	assign	adc_left_ready = 1'b1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// RX right -- select an ADC channel for the CIC downsampler
	// {{{

	// raw_rx_right
	// {{{
	always @(posedge i_clk)
	if (rx_stb)
	begin
		raw_rx_right <= raw_rx_data[RXW-1:0];
		for(ik=0; ik<NS; ik=ik+1)
		if (ik[4:0] == right_sel)
			raw_rx_right <= raw_rx_data[RXW*ik +: RXW];
	end
	// }}}

	// Right CIC
	// {{{
	asrc_cicdown #(
		.IW(RXW), .OW(RXW), .LGMEM(5), .SHIFT(11)
	) u_right_adc_cic (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_navg(4), .i_ce(rx_stb), .i_val(raw_rx_right),
		.o_ce(right_adc_cic_stb), .o_val(right_adc_cic_data)
		// }}}
	);
	// }}}

	// Right asynchronous resampler
	// {{{
	asrc_main #(
		.IW(RXW), .OW(RXW), .PFIL_TW(PFIL_TW),
		.PFIL_NCOEFFS(ADC_PFIL_NCOEFFS)
	) u_right_resampler (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		// Configuration
		// {{{
		.i_up_switch(1'b0),
		.i_cic_switch(1'b0), .i_pfil_switch(adc_sw[0]),
		.i_poly_switch(adc_sw[1]),
		.i_prefil_write(i_wb_stb && i_wb_we && i_wb_addr == ADR_ADCFIL),
		.i_prefil_tap(i_wb_data[31:32-PFIL_TW]),
		//
		.i_resample_rate(adc_resample_rate),
		// }}}
		.S_AXIS_TVALID(right_adc_cic_stb),
			.S_AXIS_TREADY(ign_right_adc_cic_ready),
			.S_AXIS_TDATA(right_adc_cic_data),
		//
		.M_AXIS_TVALID(adc_right_valid),
			.M_AXIS_TREADY(adc_right_ready),
			.M_AXIS_TDATA(adc_right_data)
		// }}}
	);

	assign	adc_right_ready = 1'b1;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Generate M_AUD* outputs
	// {{{

	reg	left_stb, right_stb;

	assign	S_TEST_TREADY = OPT_TEST_SOURCE
			&& (S_MIC_TVALID && S_MIC_TREADY && S_MIC_TLAST);

	always @(*)
	begin
		if (left_sel == 20 || left_sel == 21)
			left_stb = (S_MIC_TVALID && S_MIC_TREADY
					&& S_MIC_TLAST == left_sel[0]);
		else if (OPT_TEST_SOURCE && left_sel == 22)
			left_stb = S_TEST_TVALID && S_TEST_TREADY;
		else if (left_sel < NS)
			left_stb = adc_left_valid;
		else
			left_stb = tx_resample_valid;
	end

	always @(*)
	begin
		if (right_sel == 20 || right_sel == 21)
			right_stb = (S_MIC_TVALID && S_MIC_TREADY
					&& S_MIC_TLAST == right_sel[0]);
		else if (OPT_TEST_SOURCE && right_sel == 22)
			right_stb = S_TEST_TVALID && S_TEST_TREADY;
		else if (right_sel < NS)
			right_stb = adc_right_valid;
		else
			right_stb = tx_resample_valid;
	end

	always @(posedge i_clk)
	begin
		if (left_sel == 20 || left_sel == 21)
		begin
			if (S_MIC_TVALID && S_MIC_TREADY
						&& S_MIC_TLAST == left_sel[0])
				left_value <= S_MIC_TDATA;
		end else if (OPT_TEST_SOURCE && left_sel == 22)
			left_value <= S_TEST_TDATA;
		else if (adc_left_valid && left_sel < NS)
		begin
			if (adc_left_valid)
				left_value <= adc_left_data;
		end else if (tx_resample_valid)
			left_value <= tx_resample_data;

		if (i_pps)
		begin
			left_count <= (left_stb) ? 1:0;
			left_rate <= left_count;
		end else if (left_stb)
			left_count <= left_count + 1;
	end

	always @(posedge i_clk)
	begin
		if (right_sel == 20 || right_sel == 21)
		begin
			if (S_MIC_TVALID && S_MIC_TREADY
						&& S_MIC_TLAST == right_sel[0])
				right_value <= S_MIC_TDATA;
		end else if (OPT_TEST_SOURCE && right_sel == 22)
			right_value <= S_TEST_TDATA;
		else if (adc_right_valid && right_sel < NS)
			right_value <= adc_right_data;
		else if (tx_resample_valid)
			right_value <= tx_resample_data;

		if (i_pps)
		begin
			right_count <= (right_stb) ? 1:0;
			right_rate <= right_count;
		end else if (right_stb)
			right_count <= right_count + 1;
	end

	always @(posedge i_clk)
	if (S_MIC_TVALID && S_MIC_TREADY && S_MIC_TLAST)
		{ out_left, out_right } <= { left_value, right_value };

	always @(posedge i_clk)
	if (i_reset)
	begin
		M_AUD_TVALID <= 1'b0;
		M_AUD_TLAST  <= 1'b0;
	end else if (S_MIC_TVALID && S_MIC_TREADY)
	begin
		M_AUD_TVALID <= 1'b1;
		M_AUD_TLAST  <= S_MIC_TLAST;
	end else if (M_AUD_TREADY)
		M_AUD_TVALID <= 1'b0;

	// Left first, then right && last
	always @(posedge i_clk)
	if (S_MIC_TVALID && S_MIC_TREADY)
		M_AUD_TDATA <= (S_MIC_TLAST) ? out_right : out_left;
	// }}}

	// o_debug
	// {{{
	always @(posedge i_clk)
	begin
		o_debug <= {
			i_pps, left_stb, right_stb, rx_stb, i_pps,
			S_MIC_TVALID, S_MIC_TREADY, S_MIC_TLAST,
			M_AUD_TVALID, M_AUD_TREADY, M_AUD_TLAST,
			M_AUD_TDATA[23:24-21] };
		if (left_sel == 31)
			o_debug[1:0] <= raw_tx_data;
		if (left_sel == 30 && right_sel < NS && !M_AUD_TLAST)
			// Replace the left output side with the current
			// right input
			o_debug[20:0] <= raw_rx_right[23:24-21];
		if (right_sel == 30 && left_sel < NS && M_AUD_TLAST)
			// Replace the right output side with the current
			// left input
			o_debug[20:0] <= raw_rx_left[23:24-21];
	end
	// }}}

	//
	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, i_wb_data, ign_tx_cic_ready,
				S_TEST_TVALID,
				ign_left_adc_cic_ready,
				ign_right_adc_cic_ready };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
