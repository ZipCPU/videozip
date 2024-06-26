////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/audio/axisi2s.v
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
`default_nettype none
// }}}
module	axisi2s #(
		// {{{
		parameter	C_AXIS_DATA_WIDTH = 24,
		localparam	DW = C_AXIS_DATA_WIDTH,
		parameter	[3:0]	BDIV = 4'h1
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,	// @ 1024x BCLK freq
					S_AXI_ARESETN,
		//
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire [DW-1:0]	S_AXIS_TDATA,
		input	wire		S_AXIS_TLAST,
		//
		output	wire		M_AXIS_TVALID,
		input	wire		M_AXIS_TREADY,
		output	wire [DW-1:0]	M_AXIS_TDATA,
		output	wire		M_AXIS_TLAST,
		//
		input	wire		i_mclk,
		//
		input	wire		i_clken,
		output	wire		o_lrclk, o_bclk,
		input	wire		i_adc,
		output	wire		o_dac,
		//
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	wire [31:0]	adc_value;
	wire		stb, chan;

	reg		mclk_reset_n;
	reg	[2:0]	mclk_reset_pipe;

	wire			dac_full, dac_empty;
	wire	[2*DW-1:0]	dac_data;

	wire			ign_adc_full, adc_empty;

	reg			r_dac_valid;
	reg	[2*DW-1:0]	r_dac_data;
	wire	[DW-1:0]	this_dac_data;
	wire			dac_fifo_read;

	reg			stage_valid;
	reg	[2*DW-1:0]	stage_data;

	(* ASYNC_REG *)	reg	[4:0]	xclk_pipe;
			reg	[4:0]	xclk_debug;

	// }}}

	// MCLK reset
	// {{{
	always @(posedge i_mclk or negedge S_AXI_ARESETN)
	if (!S_AXI_ARESETN)
		{ mclk_reset_n, mclk_reset_pipe } <= 0;
	else
		{ mclk_reset_n, mclk_reset_pipe }
						<= { mclk_reset_pipe, i_clken };
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Buffer an entire packet (2 samples), before sending it through the
	// ASYNC FIFO
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// stage_valid
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		stage_valid <= 1'b0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && S_AXIS_TLAST)
		stage_valid <= 1'b1;
	else if (!dac_full)
		stage_valid <= 1'b0;
	// }}}

	// stage_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		stage_data <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		if (S_AXIS_TLAST)
			stage_data[DW-1:0]    <= S_AXIS_TDATA;
		else
			stage_data[2*DW-1:DW] <= S_AXIS_TDATA;
	end
	// }}}

	assign	S_AXIS_TREADY = !stage_valid || !dac_full;
	// }}}

	// DAC A-FIFO
	// {{{
	afifo #(
		.LGFIFO(3), .WIDTH(2*DW)
	) u_dac_fifo (
		// {{{
		.i_wclk(S_AXI_ACLK), .i_wr_reset_n(S_AXI_ARESETN),
		.i_wr(stage_valid),
		.i_wr_data({ stage_data }), .o_wr_full(dac_full),
		//
		.i_rclk(i_mclk), .i_rd_reset_n(mclk_reset_n),
		.i_rd(dac_fifo_read),
		.o_rd_data({ dac_data }), .o_rd_empty(dac_empty)
		// }}}
	);
	// }}}

	// r_dac_valid
	// {{{
	always @(posedge i_mclk)
	if (!mclk_reset_n)
		r_dac_valid <= 0;
	else if (dac_fifo_read && !dac_empty)
		r_dac_valid <= 1;
	else if (stb && chan)
		r_dac_valid <= 1'b0;
	// }}}

	assign	dac_fifo_read = !r_dac_valid || (stb && chan);

	// r_dac_data
	// {{{
	always @(posedge i_mclk)
	if (dac_fifo_read && !dac_empty)
		r_dac_data <= dac_data;
	// }}}

	assign	this_dac_data = (chan) ? r_dac_data[DW-1:0] : r_dac_data[2*DW-1:DW];

	// Low level controller
	lli2s
	lli2si(
		// {{{
		.i_mclk(i_mclk), .i_clken(mclk_reset_n),
			.i_lren(mclk_reset_n), .i_bdiv(BDIV),
		// I2S channel "clocks"
		.o_lrclk(o_lrclk), .o_bclk(o_bclk),
		.o_stb(stb), .o_chan(chan),
		// Drive the DAC, o_dac, from the incoming data dac_data
			.i_dac({ 1'b0, this_dac_data, {(31-DW){ 1'b0 }} }),
			.o_dac(o_dac),
		// Receive, from i_adc, an adc_value to return
		.i_adc(i_adc), .o_adc(adc_value)
		// }}}
	);

	// ADC A-FIFO
	// {{{
	afifo #(
		.LGFIFO(3), .WIDTH(DW+1)
	) u_adc_fifo (
		// {{{
		.i_wclk(i_mclk), .i_wr_reset_n(mclk_reset_n),
		.i_wr(stb), .i_wr_data({ chan, adc_value[30:31-DW] }),
					.o_wr_full(ign_adc_full),
		//
		.i_rclk(S_AXI_ACLK), .i_rd_reset_n(S_AXI_ARESETN && i_clken),
		.i_rd(M_AXIS_TREADY),
			.o_rd_data({ M_AXIS_TLAST, M_AXIS_TDATA }),
			.o_rd_empty(adc_empty)
		// }}}
	);

	assign	M_AXIS_TVALID = !adc_empty;
	// }}}

	always @(posedge S_AXI_ACLK)
	begin
		xclk_pipe  <= { i_mclk, o_lrclk, o_bclk, i_adc, o_dac };
		xclk_debug <= xclk_pipe;

		o_debug <= {
				M_AXIS_TVALID, 1'b0, xclk_debug, stage_valid,
				S_AXIS_TVALID, S_AXIS_TREADY, S_AXIS_TLAST,
					o_debug[20:12],//S_TDATA[DW-1:DW-9],
				M_AXIS_TVALID, M_AXIS_TREADY, M_AXIS_TLAST,
					o_debug[8:0] // M_AXIS_TDATA[DW-1:DW-9]
			};

		if (S_AXIS_TVALID)
			o_debug[20:12] <= S_AXIS_TDATA[DW-1:DW-9];
		if (M_AXIS_TVALID)
			o_debug[8:0] <= M_AXIS_TDATA[DW-1:DW-9];
	end

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, S_AXIS_TVALID, adc_value[31],
				adc_value[31-DW-1:0],
				ign_adc_full };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
