////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiiclk.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
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
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
module	xhdmiiclk(i_sys_clk, i_hdmi_raw_input_clk, i_ce, o_hs_clk,
		o_hdmi_logic_clk, o_locked);
	parameter	PHASE_BIAS = 0;
	input	wire		i_sys_clk, i_hdmi_raw_input_clk;
	input	wire		i_ce;
	output	wire		o_hs_clk;
	output	wire		o_hdmi_logic_clk;
	output	wire		o_locked;

	wire		clock_feedback, clock_feedback_buffered;
	wire	[3:0]	ignored_clk;
	wire		hs_clk_unbuffered;
	wire		logic_clk_unbuffered;

	reg	reset;
	initial	reset = 1'b1;
	always @(posedge i_sys_clk)
		reset <= !i_ce;

	PLLE2_BASE #(
		.BANDWIDTH("OPTIMIZED"),
		.CLKFBOUT_MULT(10),
		.CLKFBOUT_PHASE(PHASE_BIAS),
		.DIVCLK_DIVIDE(1),
		.STARTUP_WAIT("FALSE"),
		//
		// From my monitor, the maximum pixel clock is 210MHz.  166MHz
		// is still faster than the maximum clock I'm using, so ...we'll
		// use that as a maximum
		.CLKIN1_PERIOD(7),	// in ns, thus max pixel clk of 200MHz
		// Clock zero is the high speed clock
		.CLKOUT0_DIVIDE(2),
		.CLKOUT0_PHASE(0.0),
		.CLKOUT0_DUTY_CYCLE(0.5),
		//
		.CLKOUT1_DIVIDE(10),
		.CLKOUT1_PHASE(0.0)
		) genclki(
		.CLKIN1(i_hdmi_raw_input_clk),	// Variable rate, from HDMI input
		.CLKOUT0(hs_clk_unbuffered),
		.CLKOUT1(logic_clk_unbuffered),	// REMOVE THIS CLOCK:UNUSED
		.CLKOUT2(ignored_clk[0]),
		.CLKOUT3(ignored_clk[1]),
		.CLKOUT4(ignored_clk[2]),
		.CLKOUT5(ignored_clk[3]),
		.PWRDWN(!i_ce),
		.RST(reset),
		.CLKFBOUT(clock_feedback),
		.CLKFBIN(clock_feedback_buffered),
		.LOCKED(o_locked)
		);

	// The buffer is necessary so that the output then compensates for the
	// feedback associated with the buffer
	BUFG	hdmi_feedback_buffer(.I(clock_feedback),
			.O(clock_feedback_buffered));

	// The ISERDESE2 for the pixels requires two clock inputs, 180
	// degrees out of phase with each other.
	BUFG	hdmi_hsclk_buffer_p(.I(hs_clk_unbuffered),
				.O(o_hs_clk));

	// Also need a pixel clock, at a 0-degree phase shift
	BUFG	hdmi_hsclk_logic_buffer(.I(logic_clk_unbuffered),
				.O(o_hdmi_logic_clk));
endmodule
