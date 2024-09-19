////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/xpxclk.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Contains the Xilinx specific portions of HDMI ingestion.
//
//	Specifically, this includes:
//	1. Turning our incoming clocks from double ended to single ended via
//		a Xilinx IBUFDS.
//	2. Selecting from among three clocks for our pixel clock.  The pixel
//		clock will therefore be one of: 1) an internal 80MHz reference,
//		2) an external reference from some frequency generator (not
//		present on the Nexys Video), or 3) an external reference from
//		an external/incoming HDMI RX port.
//	3. Once selected, pixel clock is then pushed into a PLL to generate the
//		5x pixel clock signal required for HDMI.  (It's not 10x, since
//		the HDMI input/output SERDES use DDR mode, so it only needs
//		to be half that.)
//	4. The pixel clock and 5x clock are then pushed through BUFGs and
//		output.
//
//	NOTE this design uses 5 BUFGs.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
module	xpxclk #(
		parameter [0:0]	OPT_EXTERNAL_CLOCK = 1'b0
	) (
		// {{{
		input	wire		i_sysclk,
		input	wire		i_hdmirx_clk_p, i_hdmirx_clk_n,
		input	wire		i_lcl_pixclk,
		input	wire		i_siclk,
		// i_cksel == 2'b00	// Local clock
		// i_cksel == 2'b01	// Externally generated clock
		// i_cksel == 2'b10	// Incoming HDMI receive clock
		// i_cksel == 2'b11	(Reserved)
		input	wire	[1:0]	i_cksel,
		output	wire		o_hdmick_locked,
		output	wire		o_hdmirx_clk,
		output	wire		o_pixclk, o_hdmick,
		//
		// DRP port
		input	wire		i_wb_clk, i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[6:0]	i_wb_addr,
		input	wire	[31:0]	i_wb_data,
		input	wire	[3:0]	i_wb_sel,
		//
		output	wire		o_wb_stall,
		output	wire		o_wb_ack,
		output	wire	[31:0]	o_wb_data,
		//
		output	wire	[31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam [1:0]	OPT_FIXED = 2'b10,
				DEF_CKSEL = 2'b10;

	wire	lclck, hdmirx_ck, preck, siclk;
	wire	clk_fbout, clk_fb, raw_pixclk, hdmi_ck;
	// }}}
	generate if (OPT_EXTERNAL_CLOCK)
	begin : GEN_EXTERNAL_CLOCK_SW
		// Select lclck from either i_lcl_pixclk or i_siclk
		// {{{

		if (OPT_FIXED[0])
		begin : FIXED_CLKSW

			BUFG
			u_prepx (
				.I(DEF_CKSEL[0] ? i_siclk : i_lcl_pixclk),
				.O(preck));

		end else begin : CLOCK_SWITCH

			xclksw
			lclpx (
				// Clock selection
				.i_sys_clk(i_sysclk),
				.i_clk_sel(i_cksel[0]),
				// Incoming clock choices
				.i_ck0(i_lcl_pixclk), .i_ck1(i_siclk),
				// Generated output clock
				.o_clk(lclck)
			);

		end
		// }}}
	end else begin : NO_EXTERNAL_CLOCK
		assign	siclk   = i_lcl_pixclk;
		assign	lclck   = i_lcl_pixclk;
	end endgenerate

	// Select preck from either lclck or hdmirx_clk
	// {{{
	IBUFDS
	ibuf_hdmi_ck (
		.I(i_hdmirx_clk_p), .IB(i_hdmirx_clk_n), .O(hdmirx_ck)
	);

	assign	o_hdmirx_clk = hdmirx_ck;

	generate if (OPT_FIXED[1])
	begin : FIXED_CLKSW

		BUFG
		u_prepx (
			.I(DEF_CKSEL[1] ? hdmirx_ck : lclck),
			.O(preck));

	end else begin : CLOCK_SWITCH

		xclksw
		u_prepx (
			// Clock selection
			.i_sys_clk(i_sysclk),
			.i_clk_sel(i_cksel[1]),
			//
			// Incoming clock choices
			.i_ck0(lclck), .i_ck1(hdmirx_ck),
			//
			// Generated output clock
			.o_clk(preck)
		);

	end endgenerate
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Dynamic reconfiguration control
	// {{{
	wire		drp_reset, drp_den, drp_dwe, drp_drdy;
	wire	[15:0]	drp_di, drp_do;
	wire	[6:0]	drp_addr;

	reg	wb_reset;

	initial	wb_reset = 1'b1;
	always @(posedge i_wb_clk)
		wb_reset <= 1'b0;

	wbdrp #(
		.AW(7)
	) u_drp (
		// {{{
		.i_clk(i_wb_clk), .i_reset(wb_reset),
		.i_wb_cyc(i_wb_cyc), .i_wb_stb(i_wb_stb), .i_wb_we(i_wb_we),
		.i_wb_addr(i_wb_addr),
			.i_wb_data(i_wb_data), .i_wb_sel(i_wb_sel),
		.o_wb_stall(o_wb_stall), .o_wb_ack(o_wb_ack),
			.o_wb_data(o_wb_data),
		//
		.o_DEVRST(drp_reset), .o_DWE(drp_dwe), .o_DEN(drp_den),
		.o_DADDR(drp_addr), .o_DI(drp_di),
		.i_DRDY(drp_drdy), .i_DO(drp_do),
		//
		.o_debug(o_debug)
		// }}}
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// PLL locking
	// {{{
	PLLE2_ADV #(
		// {{{
		.CLKFBOUT_MULT(15),	// 100MHz * 15 = 1500MHz
		.CLKFBOUT_PHASE(0.0),
		.CLKIN1_PERIOD(10.4),	// Up to 128 MHz input
		.CLKOUT0_DIVIDE(15),	// 1500MHz / 15 => 100MHz
		.CLKOUT1_DIVIDE(3)	// 1500MHz /  5 => 500MHz
/*
		.CLKFBOUT_MULT(15),	// 80MHz * 15 = 1200MHz
		.CLKFBOUT_PHASE(0.0),
		.CLKIN1_PERIOD(12.5),	// Up to 80MHz input
		.CLKOUT0_DIVIDE(15),	// 1200MHz / 15 =>  80MHz
		.CLKOUT1_DIVIDE(3)	// 1200MHz /  3 => 400MHz
*/
		// }}}
	) u_hdmi_pll (
		// {{{
		.RST(drp_reset),
		//
		.CLKIN1(preck),		// Incoming clock
		.PWRDWN(1'b0),
		.CLKFBIN(clk_fb),
		.CLKFBOUT(clk_fbout),
		.LOCKED(o_hdmick_locked),
		//
		.CLKOUT0(raw_pixclk),
		.CLKOUT1(hdmi_ck),
		// DRP controls
		// {{{
		.DCLK(i_wb_clk),
		.DEN(drp_den),    .DWE(drp_dwe),
		.DADDR(drp_addr), .DI(drp_di),
		.DRDY(drp_drdy),  .DO(drp_do)
		// }}}

		// }}}
	);

	BUFG fdback_buf( .I(clk_fbout),  .O(clk_fb));
	BUFG pixclk_buf( .I(raw_pixclk), .O(o_pixclk));
	BUFG hdmi_buf(   .I(hdmi_ck),    .O(o_hdmick));
	// }}}
endmodule
