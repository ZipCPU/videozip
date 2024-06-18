////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/clkcounter.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Given a clock, asynchronous to the main or system clock, and
//		given a PPS strobe that is synchronous to the main clock, count
//	the number of clock ticks that take place between system clocks.
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
`timescale		1ns/1ps
`default_nettype	none
// }}}
module	clkcounter #(
		parameter	LGNAVGS = 4,
				BUSW=32,
		parameter	CLOCKFREQ_HZ = 100_000_000
	) (
		// {{{
		input	wire			i_sys_clk,
						i_tst_clk,
		input	wire			i_sys_pps,
		output	wire	[(BUSW-1):0]	o_sys_counts
		// }}}
	);

	// Local declarations
	// {{{
	reg	[(LGNAVGS-1):0]		avgs;
	(* ASYNC_REG = "TRUE" *)
	reg				q_v, qq_v;
	reg				tst_posedge;

	reg	[(BUSW-LGNAVGS-1):0]	counter;
	reg	[(BUSW-LGNAVGS-1):0]	r_sys_counts;
	wire				sys_pps;
	// }}}

	// Move the clock across clock domains
	// {{{
	always @(posedge i_tst_clk)
		avgs <= avgs + 1'b1;

	always @(posedge i_sys_clk)
		{ qq_v, q_v } <= { q_v, avgs[(LGNAVGS-1)] };

	always @(posedge i_sys_clk)
		tst_posedge <= (!qq_v)&&(q_v);
	// }}}

	// Generate a once per second pulse
	// {{{
	generate if (CLOCKFREQ_HZ > 0)
	begin : GEN_PPS
		localparam	CWID = $clog2(CLOCKFREQ_HZ+1);
		reg	[CWID-1:0]	pps_counter;
		reg			r_sys_pps;

		initial	pps_counter = 0;
		always @(posedge i_sys_clk)
		if (pps_counter >= CLOCKFREQ_HZ-1)
		begin
			pps_counter <= 0;
			r_sys_pps <= 1;
		end else begin
			pps_counter <= pps_counter + 1;
			r_sys_pps <= 0;
		end

		assign	sys_pps = r_sys_pps;

		// Keep Verilator happy
		// {{{
		// Verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_sys_pps };
		// Verilator lint_on  UNUSED
		// }}}
	end else begin : COPY_PPS
		assign	sys_pps = i_sys_pps;
	end endgenerate
	// }}}

	// Now count edges between PPS signals
	// {{{
	initial	counter = 28'h00deadc;
	always @(posedge i_sys_clk)
	if (sys_pps)
		counter <= 0;
	else if (tst_posedge)
		counter <= counter + 1'b1;

	initial	r_sys_counts = 28'hdeadbef;
	always @(posedge i_sys_clk)
	if (sys_pps)
		r_sys_counts <= counter;
	// }}}

	assign	o_sys_counts = { r_sys_counts, {(LGNAVGS){1'b0}} };
endmodule
