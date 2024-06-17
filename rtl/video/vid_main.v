////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/vid_main.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is the top level video module.  It's purpose is to take
//		an audio input, process it in one of a variety of (to be
//	determined) fashions, and then to generate from that outputs to drive
//	the three HDMI OSERDES components.
//
// Basic inputs are:
//	i_pixclk	A predefined video input clock
//	i_clk		The clock driving both the Wishbone bus and the various
//			audio channel(s) inputs.
//	Audio stream	An AXI Stream containing audio data.  THIS STREAM
//			CANNOT HANDLE BACKPRESSURE as delivered.
//
//	Control inputs shall be constant (if possible):
//		An enable signal
//		The video data size
//		Screen buffer base address in SDRAM
//		Video source selection
//	  ... but should be allowed to be overridden by an internal Wishbone
//		slave
//
// Control Registers:
//	CONTROL: 	Enable, video selection
//	BASEADDR:
//		VIDSIZE:
//		VIDPORCH
//		VIDSYNC:
//		VIDRAW:
//	(Colormap control?)
//
// Outputs:
//	Three HDMI video channels.  That's it.
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
`define	SPLIT_VIEW
// `define	USE_FFTAVG
// }}}
module	vid_main #(
		// {{{
		parameter		AW = 30, DW = 32,
		parameter [AW+$clog2(DW/8)-1:0]	DEF_BASEADDR = 32'h3ff0_0000,
					DEF_LASTADDR = 32'h4000_0000,
		parameter	LGFRAME = 16,
		// DEF_SELECT, the default video selection
		// 0: histogram, 1: trace, 2: spectrogram, 3: waterfall
`ifdef	SPLIT_VIEW
		parameter	[2:0]	DEF_SELECT   = 3'h4,
`else
		parameter	[2:0]	DEF_SELECT   = 3'h3,
`endif
		parameter [LGFRAME-1:0]	DEF_HEIGHT =  600,
					DEF_LPORCH =  601,
					DEF_LSYNC  =  605,
					DEF_LRAW   =  628,
		parameter [LGFRAME-1:0]	DEF_WIDTH  =  800,
					DEF_HPORCH =  840,
					DEF_HSYNC  =  968,
					DEF_HRAW   = 1056,
		localparam [0:0]	OPT_TUSER_IS_SOF = 1'b0
		// }}}
	) (
		// {{{
		input	wire		i_clk,
		// Verilator lint_off SYNCASYNCNET
		input	wire		i_reset,
		// Verilator lint_off SYNCASYNCNET
		input	wire		i_pixclk,
		//
		// Control information
		// {{{
		input	wire		i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire [2:0]	i_wb_addr,
		input	wire [32-1:0]	i_wb_data,
		input	wire [32/8-1:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	reg		o_wb_ack,
		output	reg [32-1:0]	o_wb_data,
		// }}}
		// The memory master channel
		// {{{
		output	wire		o_dma_cyc, o_dma_stb, o_dma_we,
		output	wire [AW-1:0]	o_dma_addr,
		output	wire [DW-1:0]	o_dma_data,
		output	wire [DW/8-1:0]	o_dma_sel,
		//
		input	wire		i_dma_stall,
		input	wire		i_dma_ack,
		input	wire [DW-1:0]	i_dma_data,
		input	wire		i_dma_err,
		// }}}
		// The incoming audio channel @ 96kHz
		// {{{
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire	[23:0]	S_AXIS_TDATA,
		// }}}
		// The outgoing video channel, @i_pixclk
		// {{{
		output	wire		o_vid_valid,
		// output	wire	[9:0]	o_vid_valid,
		output	wire	[23:0]	o_vid_data,
		output	wire		o_vid_hlast,
		output	wire		o_vid_vlast,
		//
		output	wire	[9:0]	o_hdmi_red,
		output	wire	[9:0]	o_hdmi_green,
		output	wire	[9:0]	o_hdmi_blue,
		// }}}
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[2:0]	ADR_CONTROL  = 3'h0,
				ADR_MAINBASE = 3'h1,
				ADR_SPLITBASE= 3'h2,
				ADR_SIZE     = 3'h4,
				ADR_PORCH    = 3'h5,
				ADR_SYNC     = 3'h6,
				ADR_RAW      = 3'h7;

	localparam	PW=8; // Initial pixel width
	localparam	LGFFT = 11;

	// Verilator lint_off SYNCASYNCNET
	wire		vid_reset;	// User controlled reset
	// Verilator lint_on  SYNCASYNCNET

	reg		pix_reset;
	reg	[1:0]	pix_reset_pipe;

	wire		hist_aud_valid, hist_aud_ready;
	wire	[23:0]	hist_aud_data;

	wire		trace_aud_valid, trace_aud_ready;
	wire	[23:0]	trace_aud_data;

	wire		prefft_aud_valid, prefft_aud_ready;
	wire	[23:0]	prefft_aud_data;

	wire		xclk_aud_valid, xclk_aud_ready;
	wire	[23:0]	xclk_aud_data;
	wire	xclk_aud_full, pixd_empty;


	wire		pixd_valid, pixd_ready;
	wire	[23:0]	pixd_data;

	wire	hist_valid, hist_ready, hist_last, hist_user;
	wire	[PW-1:0]	hist_data;
	wire	[31:0]		hist_debug;

	wire	trace_valid, trace_ready, trace_last, trace_user;
	wire	[PW-1:0]	trace_data;
	wire	[31:0]		trace_debug;

	wire	spgram_valid, spgram_ready, spgram_last, spgram_user;
	wire	[PW-1:0]	spgram_data;
	wire	[31:0]		spgram_debug;

	wire			wfall_cyc, wfall_stb, wfall_we;
	wire	[AW-1:0]	wfall_addr;
	wire	[DW-1:0]	wfall_wb_data;
	wire	[DW/8-1:0]	wfall_sel;
	wire			wfall_stall, wfall_ack, wfall_err;
	wire	[DW-1:0]	wfall_idata;

	wire	[31:0]		wfall_debug;

	wire			wfall_valid, wfall_ready, wfall_last,
				wfall_user;
	wire	[PW-1:0]	wfall_data;
	reg	[AW-1:0]	mem_mainbase, mem_mainlast;
	reg	[AW-1:0]	mem_splitbase, mem_splitlast;

	reg	[LGFRAME-1:0]	r_vheight, r_hwidth,
				r_vporch,  r_hporch,
				r_vsync,   r_hsync,
				r_vraw,    r_hraw;
	wire	[LGFRAME-1:0]	pix_width, pix_height;
	wire	[LGFRAME-1:0]	pix_vporch,pix_hporch,
				pix_vsync, pix_hsync,
				pix_vraw,  pix_hraw;
	reg	[2:0]		r_vid_sel;
	reg			r_user_reset, r_vid_reset;
	reg	[3:0]		r_vid_reset_timer;
	wire			ign_wb_ready, ign_pix_valid;
`ifdef	USE_FFTAVG
	reg			avg_max_hold, avg_rmbias;
	reg	[4:0]		avg_lgavg;
`endif

	// prefft_aud_* -> windw_*
	wire		fft_valid, fft_ready, fft_last;
	wire	[47:0]	fft_data;

	wire		spgram_log_valid, spgram_log_last, spgram_log_ready,
			ign_spgram_log_full, spgram_log_empty;
	wire	[7:0]	spgram_log_data;

	wire		log_valid_stb, log_last;
	wire	[7:0]	log_data;

	reg	[LGFFT-1:0]	truncate_count;
	reg			truncate_last;
	wire			truncate_stb;

	reg		wfall_log_valid, wfall_log_last;
	wire		wfall_log_ready;
	reg	[7:0]	wfall_log_data;
	wire	[23:0]	wfall_false_color;

	wire		muxd_valid, muxd_ready, muxd_last, muxd_user;
	wire	[23:0]	muxd_data;
	wire	[2:0]	muxd_select;

	wire		windw_valid, windw_ready, windw_last;
	wire	[23:0]	windw_data;

	wire		out_valid, out_ready, out_hlast, out_vlast;
	wire	[23:0]	out_data;

	wire	[2:0]		split_err;
	wire	[31:0]		split_debug;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Reset
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	vid_reset = r_vid_reset;

	initial	pix_reset = 1;
	always @(posedge i_pixclk or posedge vid_reset)
	if (vid_reset)
		{ pix_reset, pix_reset_pipe } <= -1;
	else
		{ pix_reset, pix_reset_pipe } <= { pix_reset_pipe, 1'b0 };

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Wishbone interface
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// video reset control
	// {{{
	initial	r_vid_reset  = 1'b1;
	initial	r_vid_reset_timer  = -1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_vid_reset  <= 1'b1;
		r_vid_reset_timer  <= -1;
	end else begin
		if (r_vid_reset_timer != 0)
			r_vid_reset_timer <= r_vid_reset_timer - 1;
		r_vid_reset <= (r_vid_reset_timer > 1) || r_user_reset;
	end
	// }}}

	// Mode control, video select, and video reset control
	// {{{
	initial	mem_mainbase  = DEF_BASEADDR[$clog2(DW/8) +: AW];
	initial	mem_mainlast  = DEF_BASEADDR[$clog2(DW/8) +: AW]
			+ ((DEF_LASTADDR[$clog2(DW/8) +: AW]-DEF_BASEADDR[$clog2(DW/8) +: AW]) >> 1);
	initial	mem_splitbase = DEF_BASEADDR[$clog2(DW/8) +: AW]
			+ ((DEF_LASTADDR[$clog2(DW/8) +: AW]-DEF_BASEADDR[$clog2(DW/8) +: AW]) >> 1);
	initial	mem_splitlast = DEF_LASTADDR[$clog2(DW/8) +: AW];
	initial	{ r_vheight, r_hwidth } = { DEF_HEIGHT[LGFRAME-1:0], DEF_WIDTH[LGFRAME-1:0]  };
	initial	{ r_vporch,  r_hporch } = { DEF_LPORCH[LGFRAME-1:0], DEF_HPORCH[LGFRAME-1:0] };
	initial	{ r_vsync,   r_hsync  } = { DEF_LSYNC[LGFRAME-1:0],  DEF_HSYNC[LGFRAME-1:0]  };
	initial	{ r_vraw,    r_hraw   } = { DEF_LRAW[LGFRAME-1:0],   DEF_HRAW[LGFRAME-1:0]   };
	initial	{ r_vid_reset, r_user_reset } = 2'b10;
	initial	r_vid_sel = DEF_SELECT;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		r_vid_sel <= DEF_SELECT;
		{ r_vheight, r_hwidth } <= { DEF_HEIGHT[LGFRAME-1:0], DEF_WIDTH[LGFRAME-1:0] };
		{ r_vporch,  r_hporch } <= { DEF_LPORCH[LGFRAME-1:0], DEF_HPORCH[LGFRAME-1:0] };
		{ r_vsync,   r_hsync  } <= { DEF_LSYNC[LGFRAME-1:0],  DEF_HSYNC[LGFRAME-1:0] };
		{ r_vraw,    r_hraw   } <= { DEF_LRAW[LGFRAME-1:0],   DEF_HRAW[LGFRAME-1:0] };
		r_user_reset <= 1'b0;
`ifdef	USE_FFTAVG
		avg_max_hold <= 1'b0;
		avg_rmbias   <= 1'b0;
		avg_lgavg    <= 5'h0;
`endif
		// }}}
	end else if (i_wb_stb && i_wb_we && !o_wb_stall)
	begin
		case(i_wb_addr)
		ADR_CONTROL: begin
			// {{{
			if (i_wb_sel[3]) r_user_reset <= i_wb_data[31];
`ifdef	USE_FFTAVG
			if (i_wb_sel[1])
			begin
				avg_max_hold <= i_wb_data[15];
				avg_rmbias   <= i_wb_data[14];
				avg_lgavg    <= i_wb_data[12:8];
			end
`endif
			if (i_wb_sel[0]) r_vid_sel    <= i_wb_data[2:0];
			end
			// }}}
		ADR_MAINBASE: begin
			mem_mainbase  <= i_wb_data[$clog2(DW/8) +: AW];
			end
		ADR_SPLITBASE: begin
			mem_splitbase <= i_wb_data[$clog2(DW/8) +: AW];
			end
		ADR_SIZE: if (r_user_reset) begin
			// {{{
		if (i_wb_sel[3])	r_vheight[15:8] <= i_wb_data[31:24];
		if (i_wb_sel[2])	r_vheight[ 7:0] <= i_wb_data[23:16];
		if (i_wb_sel[1])	r_hwidth[15:8]  <= i_wb_data[15: 8];
		if (i_wb_sel[0])	r_hwidth[ 7:0]  <= i_wb_data[ 7: 0];
			end
			// }}}
		ADR_PORCH: if (r_user_reset) begin
			// {{{
		if (i_wb_sel[3])	r_vporch[15:8] <= i_wb_data[31:24];
		if (i_wb_sel[2])	r_vporch[ 7:0] <= i_wb_data[23:16];
		if (i_wb_sel[1])	r_hporch[15:8] <= i_wb_data[15: 8];
		if (i_wb_sel[0])	r_hporch[ 7:0] <= i_wb_data[ 7: 0];
			end
			// }}}
		ADR_SYNC: if (r_user_reset) begin
			// {{{
		if (i_wb_sel[3])	r_vsync[15:8] <= i_wb_data[31:24];
		if (i_wb_sel[2])	r_vsync[ 7:0] <= i_wb_data[23:16];
		if (i_wb_sel[1])	r_hsync[15:8] <= i_wb_data[15: 8];
		if (i_wb_sel[0])	r_hsync[ 7:0] <= i_wb_data[ 7: 0];
			end
			// }}}
		ADR_RAW: if (r_user_reset) begin
			// {{{
		if (i_wb_sel[3])	r_vraw[15:8] <= i_wb_data[31:24];
		if (i_wb_sel[2])	r_vraw[ 7:0] <= i_wb_data[23:16];
		if (i_wb_sel[1])	r_hraw[15:8] <= i_wb_data[15: 8];
		if (i_wb_sel[0])	r_hraw[ 7:0] <= i_wb_data[ 7: 0];
			end
			// }}}
		default: begin end
		endcase
	end

	always @(posedge i_clk)
		mem_mainlast <= mem_mainbase
			+ ((DEF_LASTADDR[$clog2(DW/8) +: AW]-DEF_BASEADDR[$clog2(DW/8) +: AW]) >> ($clog2(DW/8)+1));
	always @(posedge i_clk)
		mem_splitlast <= mem_splitbase
			+ ((DEF_LASTADDR[$clog2(DW/8) +: AW]-DEF_BASEADDR[$clog2(DW/8) +: AW]) >> ($clog2(DW/8)+1));
	// }}}

	// o_wb_data
	// {{{
	always @(posedge i_clk)
	begin
		o_wb_data <= 0;
		case(i_wb_addr)
		3'h0: begin
			o_wb_data <= { r_user_reset, split_err, 4'h0,
					16'h0, 5'h0, r_vid_sel };
`ifdef	USE_FFTAVG
			o_wb_data[15:8] <= { avg_max_hold, avg_rmbias, 1'b0, avg_lgavg };
`endif
			end
		ADR_MAINBASE: begin
			o_wb_data[$clog2(DW/8) +: AW] <= mem_mainbase;
			end
		ADR_SPLITBASE: begin
			o_wb_data[$clog2(DW/8) +: AW] <= mem_splitbase;
			end
		ADR_SIZE:  o_wb_data <= { r_vheight, r_hwidth };
		ADR_PORCH: o_wb_data <= { r_vporch,  r_hporch };
		ADR_SYNC:  o_wb_data <= { r_vsync,   r_hsync  };
		ADR_RAW:   o_wb_data <= { r_vraw,    r_hraw   };
		default: begin end
		endcase

		if (!i_wb_stb || i_wb_we)
			o_wb_data <= 0;
	end
	// }}}

	assign	o_wb_stall = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= !i_reset && i_wb_stb && !o_wb_stall;

	//
	// Move the video mode values from WB to PIX clock
	//
	// assign	pix_height = r_vheight;
	// assign	pix_width  = r_hwidth;

	tfrvalue #(
		// {{{
		.W(3 + LGFRAME*8), .DEFAULT({ DEF_SELECT,
			DEF_HEIGHT[LGFRAME-1:0], DEF_WIDTH[LGFRAME-1:0],
			DEF_LPORCH[LGFRAME-1:0], DEF_HPORCH[LGFRAME-1:0],
			DEF_LSYNC[LGFRAME-1:0],  DEF_HSYNC[LGFRAME-1:0],
			DEF_LRAW[LGFRAME-1:0],   DEF_HRAW[LGFRAME-1:0]   })
		// }}}
	) tfr_vidmode (
		// {{{
		.i_a_clk(i_clk), .i_a_reset_n(!r_vid_reset),
		.i_a_valid(1'b1), .o_a_ready(ign_wb_ready),
		.i_a_data({ r_vid_sel,
			    r_vheight, r_hwidth,
			    r_vporch,  r_hporch,
			    r_vsync,   r_hsync,
			    r_vraw,    r_hraw   }),
		.i_b_clk(i_pixclk), .i_b_reset_n(!pix_reset),
		.o_b_valid(ign_pix_valid), .i_b_ready(1'b1),
		.o_b_data({ muxd_select,
			    pix_height,  pix_width,
			    pix_vporch,  pix_hporch,
			    pix_vsync,   pix_hsync,
			    pix_vraw,    pix_hraw   })
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// AXI Stream audio broadcast
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	//
	// Split the incoming audio stream into multiple feed streams for each
	// of the various IPs
	//

	axisbroadcast #(
		// {{{
		.NM(2), .C_AXIS_DATA_WIDTH(24)
		// }}}
	) u_broadcast_clk (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!i_reset),
		.S_AXIS_TVALID(S_AXIS_TVALID), .S_AXIS_TREADY(S_AXIS_TREADY),
			.S_AXIS_TDATA(S_AXIS_TDATA),

		.M_AXIS_TVALID({ prefft_aud_valid, xclk_aud_valid }),
			.M_AXIS_TREADY({ prefft_aud_ready, xclk_aud_ready }),
			.M_AXIS_TDATA({ prefft_aud_data, xclk_aud_data })
		// }}}
	);

	assign	xclk_aud_ready = !xclk_aud_full;
	assign	pixd_valid = !pixd_empty;
	// Some of our streams need the data in the pixel clock domain
	// already, so let's cross clocks
	afifo #(
		.WIDTH(24)
	) u_hist_afifo (
		// {{{
		.i_wclk(i_clk), .i_wr_reset_n(!r_vid_reset),
			.i_wr(xclk_aud_valid),
			.i_wr_data(xclk_aud_data),
			.o_wr_full(xclk_aud_full),
		//
		.i_rclk(i_pixclk), .i_rd_reset_n(!pix_reset),
			.i_rd(pixd_ready),
			.o_rd_data(pixd_data),
			.o_rd_empty(pixd_empty)
		// }}}
	);

	axisbroadcast #(
		// {{{
		.NM(2), .C_AXIS_DATA_WIDTH(24)
		// }}}
	) u_broadcast_pix (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		.S_AXIS_TVALID(pixd_valid), .S_AXIS_TREADY(pixd_ready),
			.S_AXIS_TDATA(pixd_data),

		.M_AXIS_TVALID({ trace_aud_valid, hist_aud_valid }),
			.M_AXIS_TREADY({ trace_aud_ready, hist_aud_ready }),
			.M_AXIS_TDATA({ trace_aud_data, hist_aud_data })
		// }}}
	);


	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Histogram
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	vid_histogram #(
		// .LGHIST(LGHIST)
		.LGDIM(LGFRAME), .PW(PW), .ACTIVE_PIXEL({(PW){1'b1}}),
		.LINE_PIXEL(8'h20),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
	) u_histogram (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		.S_AXIS_TVALID(hist_aud_valid),.S_AXIS_TREADY(hist_aud_ready),
		.S_AXIS_TDATA(hist_aud_data[23:16]),
		//
		.M_VID_VALID(hist_valid), .M_VID_READY(hist_ready),
		.M_VID_DATA(hist_data), .M_VID_LAST(hist_last),
		.M_VID_USER(hist_user),
		//
		.i_height(pix_height), .i_width(pix_width)
		// }}}
	);

	// hist_debug =
	//	hist_aud_valid, hist_aud_ready, hist_aud_data[23:16]
	//	hist_valid, hist_ready, hist_last, hist_user,
	//	(hist_data == {(PW){1'b1}}), (hist_data == 8'h20)
	//	=> 16b of data
	// but ... this needs to cross from the pixel to the bus clock domains

	assign	hist_debug = 32'h0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Trace
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	vid_trace #(
		// {{{
		.PW(PW), .IW(24),
		.DEF_VSCALE({9'h01,{(LGFRAME-9){1'b0}} }),
		.OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF),
		.LGLEN(10), .LGFRAME(LGFRAME),
		.BACKGROUND_COLOR(8'h00), .AXIS_COLOR(8'h30),
		.LINE_COLOR(8'hc8), .OPT_UNSIGNED(1'b0), .OPT_FRAMED(1'b0),
		.OPT_TRUNCATE_WIDTH(1'b0)
		// }}}
	) u_trace (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		//
		.i_trigger_en(1'b0), .i_trigger(1'b0), .i_trigger_reset(1'b1),
		//
		.i_width(pix_width), .i_height(pix_height),
		//
		.S_AXIS_TVALID(trace_aud_valid),.S_AXIS_TREADY(trace_aud_ready),
		.S_AXIS_TDATA(trace_aud_data), .S_AXIS_TLAST(1'b0),
		//
		.M_VID_VALID(trace_valid), .M_VID_READY(trace_ready),
		.M_VID_DATA(trace_data), .M_VID_LAST(trace_last),
		.M_VID_USER(trace_user)
		// }}}
	);

	// trace_debug <= { trace_aud_valid, trace_aud_ready,
	//		trace_aud_data[23:8],
	//	trace_valid, trace_ready, trace_last, trace_user, trace_data }
	//	=> 14b
	assign	trace_debug = 32'h0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Spectrum & FFT
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	axis_windowfn #(
		// {{{
		.IW(24), .OW(24), .TW(16), .LGNFFT(LGFFT),
		.OPT_FIXED_TAPS(1),
// `define	HIRES
`ifdef	HIRES
		.OPT_HIRES(1'b1),
		.INITIAL_COEFFS("f3.hex")
`else
		.OPT_HIRES(1'b0),
		.INITIAL_COEFFS("hanning.hex")
`endif
		// }}}
	) u_windowfn (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		//
		.i_tap_wr(1'b0), .i_tap(16'h0),
		//
		.i_tvalid(prefft_aud_valid), .o_tready(prefft_aud_ready),
		.i_tdata(prefft_aud_data),
		//
		.o_tvalid(windw_valid), .i_tready(windw_ready),
		.o_tdata(windw_data), .o_tlast(windw_last)
		// }}}
	);

	// FFT
	axis_fft #(
		// {{{
		// Note: THESE NUMBERS MUST MATCH HOW THE INTERNAL FFT WAS BUILT
		// .LGWIDTH(LGFFT), .IW(24), .OW(24)
		.LGWIDTH(LGFFT), .IW(19), .OW(24), .NCK(3)
		// }}}
	) u_fft (
		// {{{
		.i_clk(i_clk), .i_reset_n(!i_reset),
		//
		.i_tvalid(windw_valid), .o_tready(windw_ready),
		.i_tdata( { windw_data[23:5], 19'h0 }), .i_tlast( windw_last),
		//
		.o_tvalid(fft_valid), .i_tready(fft_ready),
		.o_tdata(fft_data),   .o_tlast(fft_last)
		// }}}
	);


`ifdef	USE_FFTAVG
	reg		avg_max_hold;
	reg	[4:0]	avg_lgavg;
	reg		avg_rmbias;

	fftavg #(
		.IW(16), .LGFFT(LGFFT) //, .OW(2*IW+1) or 32bits
	) u_fftavg (
		// {{{
		.S_AXI_ACLK(i_clk), .S_AXI_ARESETN(!vid_reset),
		//
		.i_max_hold(avg_max_hold), .i_lgavg(avg_lgavg),
			.i_rmbias(avg_rmbias),
		//
		.S_AXIS_TVALID(fft_valid), .S_AXIS_TREADY(fft_ready),
			.S_AXIS_TDATA({ fft_data[47:32], fft_data[23:8] }),
			.S_AXIS_TLAST(fft_last),
		//
		.M_AXIS_TVALID(log_valid_stb), .M_AXIS_TREADY(1'b1),
			.M_AXIS_TDATA(log_data), .M_AXIS_TLAST(log_last)
		// }}}
	);
`else
	// LOG
	wire	log_valid;

	logfn_axis #(
		// .IW(24), .OW(8)
	) u_log (
		// {{{
		.i_clk(i_clk), .i_reset(vid_reset),
		.i_ce(fft_valid && fft_ready), .i_sync(fft_last),
		.i_real(fft_data[47:32]), .i_imag(fft_data[23:8]),
		.o_valid(log_valid),
		.o_sample(log_data), .o_sync(log_last)
		// }}}
	);

	assign	fft_ready = 1'b1; // !log_valid || log_ready;
	assign	log_valid_stb = log_valid && fft_valid && fft_ready;
`endif

	// Truncate the FFT to the first half only
	// {{{
	assign			truncate_stb = log_valid_stb && !truncate_count[LGFFT-1];

	always @(posedge i_clk)
	if (r_vid_reset)
		truncate_count <= 0;
	else if (log_valid_stb)
	begin
		if (!truncate_count[LGFFT-1])
			truncate_count <= truncate_count + 1;
		if (log_last)
			truncate_count <= 0;
	end

	always @(posedge i_clk)
	if (r_vid_reset)
		truncate_last <= 0;
	else if (log_valid_stb)
	begin
		truncate_last <= (truncate_count + 2 >= (1<<(LGFFT-1)));

		if (log_last)
			truncate_last <= 1'b0;
	end
	// }}}

	afifo #(
		.WIDTH(9)
	) u_spgram_afifo (
		// {{{
		.i_wclk(i_clk), .i_wr_reset_n(!r_vid_reset),
			.i_wr(truncate_stb),
			.i_wr_data({ truncate_last, log_data }),
			.o_wr_full(ign_spgram_log_full),
		//
		.i_rclk(i_pixclk), .i_rd_reset_n(!pix_reset),
			.i_rd(spgram_log_ready),
			.o_rd_data({ spgram_log_last, spgram_log_data }),
			.o_rd_empty(spgram_log_empty)
		// }}}
	);

	assign	spgram_log_valid = !spgram_log_empty;

	vid_trace #(
		// {{{
		.PW(PW), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF), .IW(8),
		.LGFRAME(LGFRAME), .OPT_FRAMED(1'b1), .OPT_UNSIGNED(1'b1),
		.OPT_TRUNCATE_WIDTH(1'b1)
		// }}}
	) u_spectrogram (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		//
		.i_trigger_en(1'b0), .i_trigger(1'b0), .i_trigger_reset(1'b1),
		//
		.i_width(pix_width), .i_height(pix_height),
		//
		.S_AXIS_TVALID(spgram_log_valid),.S_AXIS_TREADY(spgram_log_ready),
		.S_AXIS_TDATA(spgram_log_data),.S_AXIS_TLAST(spgram_log_last),
		//
		.M_VID_VALID(spgram_valid), .M_VID_READY(spgram_ready),
		.M_VID_DATA(spgram_data), .M_VID_LAST(spgram_last),
		.M_VID_USER(spgram_user)
		// }}}
	);

	assign	spgram_debug = 32'h0;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Waterfall display
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// wfall_log_valid
	// {{{
	initial	wfall_log_valid = 0;
	always @(posedge i_clk)
	if (vid_reset)
		wfall_log_valid <= 0;
	else if (truncate_stb)
		wfall_log_valid <= 1;
	else if (wfall_log_ready)
		wfall_log_valid <= 0;
	// }}}

	// wfall_log_data
	// {{{
	always @(posedge i_clk)
	if (truncate_stb)
	begin
		wfall_log_data <= log_data;
		wfall_log_last <= truncate_last;
	end
	// }}}

	vid_waterfall #(
		.LGFRAME(LGFRAME), .PW(PW), .DW(DW),
		.AW(AW), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
	) u_waterfall (
		// {{{
		.i_pixclk(i_pixclk),
		//
		.i_baseaddr(mem_mainbase), .i_lastaddr(mem_mainlast),
		.i_en(r_vid_sel == 3'h3),
		//
		.i_width(r_hwidth), .i_height(r_vheight),
		// Incoming log data to be pixellated
		// {{{
		.S_AXIS_TVALID(wfall_log_valid),.S_AXIS_TREADY(wfall_log_ready),
		.S_AXIS_TDATA(wfall_log_data),.S_AXIS_TLAST(wfall_log_last),
		// }}}
		.i_clk(i_clk), .i_reset(i_reset),
		// The memory master channel
		// {{{
		.o_wb_cyc(wfall_cyc), .o_wb_stb(wfall_stb), .o_wb_we(wfall_we),
		.o_wb_addr(wfall_addr), .o_wb_data(wfall_wb_data),
			.o_wb_sel(wfall_sel),
		//
		.i_wb_stall(wfall_stall),
		.i_wb_ack(wfall_ack),
		.i_wb_data(wfall_idata),
		.i_wb_err(wfall_err),
		// }}}
		// Outgoing video (pixel) stream
		// {{{
		.M_VID_TVALID(wfall_valid), .M_VID_TREADY(wfall_ready),
		.M_VID_TDATA(wfall_data), .M_VID_TLAST(wfall_last),
		.M_VID_TUSER(wfall_user),
		// }}}
		//
		.o_debug(wfall_debug)
		// }}}
	);

	vid_clrmap
	u_clrmap (
		.i_pixel(wfall_data),
		.o_r(wfall_false_color[23:16]),
		.o_g(wfall_false_color[15: 8]),
		.o_b(wfall_false_color[ 7: 0])
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Split display
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	SPLIT_VIEW
	wire			split_cyc, split_stb, split_we;
	wire	[AW-1:0]	split_addr;
	wire	[DW-1:0]	split_wb_data;
	wire	[DW/8-1:0]	split_sel;
	wire			split_stall, split_ack, split_bus_err;
	wire	[DW-1:0]	split_idata;
	wire	[2:0]		w_split_err;
	reg	[2:0]		r_split_err;

	reg			split_log_valid, split_log_last;
	wire			split_log_ready;
	reg	[7:0]		split_log_data;

	wire			split_valid, split_ready, split_last,split_user;
	wire	[23:0]		split_data;

	// split_log_valid
	// {{{
	initial	split_log_valid = 0;
	always @(posedge i_clk)
	if (vid_reset)
		split_log_valid <= 0;
	else if (truncate_stb)
		split_log_valid <= 1;
	else if (split_log_ready)
		split_log_valid <= 0;
	// }}}

	// split_log_data, split_log_last
	// {{{
	always @(posedge i_clk)
	if (truncate_stb)
	begin
		split_log_data <= log_data;
		split_log_last <= truncate_last;
	end
	// }}}

	vid_split #(
		// {{{
		.LGFRAME(LGFRAME), // .PW(PW),
		.AW(AW), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF), .DW(DW)
		// }}}
	) u_split (
		// {{{
		.i_pixclk(i_pixclk), .i_pix_reset(pix_reset),
		//
		.i_baseaddr(mem_splitbase), .i_lastaddr(mem_splitlast),
		.i_en(r_vid_sel == 3'h4),
		.o_split_err(w_split_err),
		//
		.i_width(r_hwidth), .i_height(r_vheight),
		// Incoming log data to be pixellated
		// {{{
		.S_AXIS_TVALID(split_log_valid),.S_AXIS_TREADY(split_log_ready),
		.S_AXIS_TDATA(split_log_data),.S_AXIS_TLAST(split_log_last),
		// }}}
		.i_clk(i_clk), .i_reset(i_reset),
		// The memory master channel
		// {{{
		.o_wb_cyc(split_cyc), .o_wb_stb(split_stb), .o_wb_we(split_we),
		.o_wb_addr(split_addr),
		.o_wb_data(split_wb_data),
		.o_wb_sel(split_sel),
		//
		.i_wb_stall(split_stall),
		.i_wb_ack(split_ack),
		.i_wb_data(split_idata),
		.i_wb_err(split_bus_err),
		// }}}
		// Outgoing video (pixel) stream
		// {{{
		.M_VID_VALID(split_valid), .M_VID_READY(split_ready),
		.M_VID_DATA(split_data), .M_VID_LAST(split_last),
		.M_VID_USER(split_user),
		//
		.o_debug(split_debug)
		// }}}
		// }}}
	);

	wbarbiter #(
		.DW(DW), .AW(AW)
	) u_arbiter (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_a_cyc(wfall_cyc), .i_a_stb(wfall_stb), .i_a_we(wfall_we),
		.i_a_adr(wfall_addr), .i_a_dat(wfall_wb_data),
			.i_a_sel(wfall_sel),
		.o_a_stall(wfall_stall),.o_a_ack(wfall_ack),.o_a_err(wfall_err),
		//
		.i_b_cyc(split_cyc), .i_b_stb(split_stb), .i_b_we(split_we),
		.i_b_adr(split_addr), .i_b_dat(split_wb_data),
			.i_b_sel(split_sel),
		.o_b_stall(split_stall),.o_b_ack(split_ack),.o_b_err(split_bus_err),
		//
		.o_cyc(o_dma_cyc), .o_stb(o_dma_stb), .o_we(o_dma_we),
		.o_adr(o_dma_addr), .o_dat(o_dma_data),.o_sel(o_dma_sel),
		.i_stall(i_dma_stall),.i_ack(i_dma_ack),.i_err(i_dma_err)
		// }}}
	);

	assign	wfall_idata = i_dma_data;
	assign	split_idata = i_dma_data;

	reg	[30:0]	split_err_clear_counter;
	always @(posedge i_clk)
	if (i_reset || r_vid_reset)
	begin
		split_err_clear_counter <= 0;
		r_split_err <= 0;
	end else if (|w_split_err)
	begin
		r_split_err <= r_split_err | split_err;
		split_err_clear_counter <= 0;
	end else if (r_split_err != 0)
	begin
		if (&split_err_clear_counter)
			r_split_err <= 0;
		split_err_clear_counter <= split_err_clear_counter + 1;
	end

	assign	split_err = r_split_err;
`else
	assign	o_dma_cyc  = wfall_cyc;
	assign	o_dma_stb  = wfall_stb;
	assign	o_dma_we   = wfall_we;
	assign	o_dma_addr = wfall_addr;
	assign	o_dma_data = wfall_wb_data;
	assign	o_dma_sel  = wfall_sel;

	assign	wfall_stall = i_dma_stall;
	assign	wfall_ack   = i_dma_ack;
	assign	wfall_idata = i_dma_data;
	assign	wfall_err   = i_dma_err;

	assign	split_err = 3'h0;
	assign	split_debug = 32'h0;
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Select from among multiple potential video sources
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	vid_mux #(
`ifdef	SPLIT_VIEW
		.NIN(5), .DEF_SELECT(DEF_SELECT),
`else
		.NIN(4), .DEF_SELECT(DEF_SELECT[1:0]),
`endif
		.LGDIM(LGFRAME), .PW(24), .OPT_TUSER_IS_SOF(OPT_TUSER_IS_SOF)
	) u_vidmux (
		// {{{
		.S_AXI_ACLK(i_pixclk), .S_AXI_ARESETN(!pix_reset),
		//
`ifdef	SPLIT_VIEW
		.S_VID_VALID({split_valid, wfall_valid,spgram_valid,trace_valid,hist_valid}),
		.S_VID_READY({split_ready, wfall_ready,spgram_ready,trace_ready,hist_ready}),
		.S_VID_DATA({ split_data, wfall_false_color, {(3){spgram_data}},
					{(3){trace_data}}, {(3){hist_data}} }),
		.S_VID_LAST({ split_last, wfall_last, spgram_last, trace_last, hist_last }),
		.S_VID_USER({ split_user, wfall_user, spgram_user, trace_user, hist_user }),
		//
		.i_select(muxd_select),
`else
		.S_VID_VALID({wfall_valid,spgram_valid,trace_valid,hist_valid}),
		.S_VID_READY({wfall_ready,spgram_ready,trace_ready,hist_ready}),
		.S_VID_DATA({ wfall_false_color, {(3){spgram_data}},
					{(3){trace_data}}, {(3){hist_data}} }),
		.S_VID_LAST({ wfall_last, spgram_last, trace_last, hist_last }),
		.S_VID_USER({ wfall_user, spgram_user, trace_user, hist_user }),
		//
		.i_select(muxd_select[1:0]),
`endif
		//
		.M_VID_VALID(muxd_valid), .M_VID_READY(muxd_ready),
		.M_VID_DATA(muxd_data), .M_VID_LAST(muxd_last),
		.M_VID_USER(muxd_user)
		// }}}
	);

	assign	out_valid = muxd_valid;
	assign	muxd_ready= out_ready;
	assign	out_data  = muxd_data;
	assign	out_vlast = muxd_last;
	assign	out_hlast = muxd_user;

	always @(posedge i_clk)
	case(muxd_select)
	3'h0: o_debug <= hist_debug;
	3'h1: o_debug <= trace_debug;
	3'h2: o_debug <= spgram_debug;
	3'h3: o_debug <= wfall_debug;
	3'h4: o_debug <= split_debug;
	default: o_debug <= 32'h0;
	endcase

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Convert the out* stream to HDMI
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	o_vid_valid = out_valid && out_ready;
	assign	o_vid_data  = out_data;
	assign	o_vid_hlast = out_hlast;
	assign	o_vid_vlast = out_vlast;

	axishdmi #(
		.HW(LGFRAME), .VW(LGFRAME),
		.OPT_RESYNC_ON_VLAST(1'b0)
	) u_axishdmi (
		// {{{
		.i_pixclk(i_pixclk), .i_reset(pix_reset),
		// Video stream input
		.i_valid(out_valid), .o_ready(out_ready),
		.i_hlast(out_hlast), .i_vlast(out_vlast),
		.i_rgb_pix(out_data),	// *MUST* be 24-bit color here
		// Mode information
		.i_hm_width(pix_width), .i_hm_porch(pix_hporch),
		.i_hm_synch(pix_hsync), .i_hm_raw(pix_hraw),
		.i_hm_syncpol(1'b1),
		//
		.i_vm_height(pix_height),.i_vm_porch(pix_vporch),
		.i_vm_synch(pix_vsync),  .i_vm_raw(pix_vraw),
		.i_vm_syncpol(1'b1),
		// HDMI outputs
		.o_red(o_hdmi_red), .o_grn(o_hdmi_green), .o_blu(o_hdmi_blue)
		// }}}
	);

	// }}}

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_wb_cyc, trace_aud_data, hist_aud_data,
			ign_pix_valid, ign_wb_ready,
			ign_spgram_log_full,
			DEF_BASEADDR[$clog2(DW/8)-1:0],
			DEF_LASTADDR[$clog2(DW/8)-1:0],
`ifndef	SPLIT_VIEW
			muxd_select[2],
`endif
			mem_splitbase, mem_splitlast, fft_data,
			windw_data };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
