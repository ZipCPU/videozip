////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/axincdc.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Move packets across clock domains.  Both interfaces need to
//		be at less than 100% utilization to be successful.  This will
//	often require expanding the packet from X bits / clock to
//	2X bits / clock or more prior to entering (or after leaving) this
//	module.
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
`timescale 1ns/1ps
// }}}
module axincdc #(
		// {{{
		parameter	DW=32,		// Bits per beat
		localparam	LGBYTES = (DW <= 8) ? 1 : $clog2(DW/8),
		parameter	LGFIFO = 4	// Async FIFO size (log_2)
		// }}}
	) (
		// {{{
		// Incoming packet data from one interface
		// {{{
		input	wire			S_CLK, S_ARESETN,
		//
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[DW-1:0]	S_DATA,
		input	wire	[LGBYTES-1:0]	S_BYTES,
		input	wire			S_ABORT,
		input	wire			S_LAST,
		// }}}
		// Outgoing packet data
		// {{{
		input	wire			M_CLK, M_ARESETN,
		//
		output	wire			M_VALID,
		input	wire			M_READY,
		output	wire	[DW-1:0]	M_DATA,
		output	wire	[LGBYTES-1:0]	M_BYTES,
		output	wire			M_ABORT,
		output	wire			M_LAST
		// }}}
		// }}}
	);

	localparam	FW = DW + $clog2(DW/8) + 1;
	wire	w_full, w_empty, w_abort;
	reg	s_midpkt, s_abort;
	wire	[FW-1:0]	wr_data, rd_data;

	// Incoming skidbuffer
	// {{{
	localparam [0:0]	OPT_SKIDBUFFER = 1'b1;
	wire			skd_valid, skd_last, skd_abort, skd_ready;
	wire	[DW-1:0]	skd_data;
	wire	[LGBYTES-1:0]	skd_bytes;

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER
		wire	[DW+$clog2(DW/8)-1:0]	skd_in, skd_out;

		netskid #(
			.DW(DW + $clog2(DW/8))
		) u_netskid (
			.i_clk(S_CLK), .i_reset(!S_ARESETN),
			//
			.S_AXIN_VALID(S_VALID), .S_AXIN_READY(S_READY),
			.S_AXIN_DATA(skd_in),
			.S_AXIN_LAST(S_LAST), .S_AXIN_ABORT(S_ABORT),
			//
			.M_AXIN_VALID(skd_valid), .M_AXIN_READY(skd_ready),
			.M_AXIN_DATA(skd_out),
			.M_AXIN_LAST(skd_last), .M_AXIN_ABORT(skd_abort)
		);

		assign	skd_data  = skd_out[DW-1:0];
		if (DW <= 8)
		begin : NO_SKD_BYTES
			assign	skd_in = S_DATA;
			assign	skd_bytes = 0;
			// Keep Verilator happy
			// Verilator lint_off UNUSED
			wire	unused_wrdata;
			assign	unused_wrdata = &{ 1'b0, S_BYTES };
			// Verilator lint_on  UNUSED
		end else begin : COUNT_SKD_BYTES
			assign	skd_in = { S_BYTES, S_DATA };
			assign	skd_bytes = skd_out[DW +: $clog2(DW/8)];
		end

	end else begin : NO_SKIDBUFFER
		assign	skd_valid = S_VALID;
		assign	S_READY   = skd_ready;
		assign	skd_data  = S_DATA;
		assign	skd_bytes = S_BYTES;
		assign	skd_last  = S_LAST;
		assign	skd_abort = S_ABORT;
	end endgenerate
	// }}}

	// s_midpkt
	// {{{
	always @(posedge S_CLK)
	if (!S_ARESETN)
		s_midpkt <= 1'b0;
	else if (skd_abort && (!skd_valid || skd_ready))
		s_midpkt <= 1'b0;
	else if (skd_valid && skd_ready)
		s_midpkt <= !skd_last;
	// }}}

	// s_abort
	// {{{
	always @(posedge S_CLK)
	if (S_ARESETN)
		s_abort <= 1'b0;
	else if (!w_full)
		s_abort <= 1'b0;
	else if (s_midpkt && skd_abort && (!skd_valid || skd_ready))
		s_abort <= 1'b1;
	// }}}

	generate if (DW <= 8)
	begin : WR_BYTE_DATA
		assign	wr_data = { skd_last, skd_data };

		// Keep Verilator happy
		// Verilator lint_off UNUSED
		wire	unused_wrdata;
		assign	unused_wrdata = &{ 1'b0, skd_bytes };
		// Verilator lint_on  UNUSED
	end else begin : GEN_WR_DATA
		assign	wr_data = { skd_last, skd_bytes, skd_data };
	end endgenerate

	afifo #(
		.LGFIFO(LGFIFO),
		.WIDTH(1+FW)
	) u_afifo (
		// {{{
		.i_wclk(S_CLK),		.i_wr_reset_n(S_ARESETN),
		.i_wr(s_abort || (skd_valid && !skd_abort ) || (skd_abort && s_midpkt)),
		.i_wr_data({ s_abort || (skd_abort && s_midpkt), wr_data }),
		.o_wr_full(w_full),
		//
		.i_rclk(M_CLK),		.i_rd_reset_n(M_ARESETN),
		.i_rd(M_READY),
		.o_rd_data({ w_abort, rd_data }),
		.o_rd_empty(w_empty)
		// }}}
	);

	assign	M_DATA = rd_data[DW-1:0];
	assign	M_LAST = rd_data[$clog2(DW/8) + DW];
	generate if (DW<= 8)
	begin : RD_NOBYTES
		assign	M_BYTES = 1'b1;
	end else begin : RD_BYTES
		assign	M_BYTES = rd_data[DW +: $clog2(DW/8)];
	end endgenerate

	assign	M_VALID = !w_empty;
	assign	skd_ready = skd_abort || (!w_full && !s_abort);
	assign  M_ABORT = w_abort && M_VALID;
endmodule
