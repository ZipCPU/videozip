////////////////////////////////////////////////////////////////////////////////
//
// Filename:	wbdrp.txt
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Control an MMCM/PLL Dynamic Reconfiguration Port (DRP) from
//		Wishbone.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
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
`timescale 1ns/1ps
`default_nettype none
// }}}
module	wbdrp #(
		parameter	AW = 6
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_wb_cyc, i_wb_stb, i_wb_we,
		input	wire	[AW-1:0]	i_wb_addr,
		input	wire	[31:0]		i_wb_data,
		input	wire	[3:0]		i_wb_sel,
		//
		output	wire			o_wb_stall,
		output	reg			o_wb_ack,
		output	reg	[31:0]		o_wb_data,
		//
		output	reg			o_DEVRST,
		output	reg			o_DWE, o_DEN,
		output	reg	[AW-1:0]	o_DADDR,
		output	reg	[15:0]		o_DI,
		input	wire	[15:0]		i_DO,
		input	wire			i_DRDY,
		// output wire o_DCLK = i_clk
		//
		// reset and locked are controlled and managed elsewhere
		output	reg	[31:0]		o_debug
		// }}}
	);

	// Local declarations
	// {{{
	localparam [1:0]	DRP_IDLE = 2'b00,
				DRP_READ = 2'b01,
				DRP_AND  = 2'b10,
				DRP_WRITE= 2'b11;

	reg	[1:0]	fsm_state;
	reg	[15:0]	r_mask, r_data;
	reg		r_will_ack;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Connection logic
	// {{{

	// o_DEVRST
	// {{{
	initial	o_DEVRST = 1'b1;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		o_DEVRST <= 1'b0;
	else if (i_wb_stb && !o_wb_stall)
		o_DEVRST <= o_DEVRST || i_wb_we;
	else if (o_wb_ack)
		o_DEVRST <= 1'b0;
	// }}}

	// r_will_ack
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc)
		r_will_ack <= 1'b0;
	else if (i_wb_stb && !o_wb_stall)
		r_will_ack <= 1'b1;
	else if (o_wb_ack)
		r_will_ack <= 1'b0;
	// }}}

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		fsm_state <= DRP_IDLE;
		o_wb_ack  <= 1'b0;
		o_wb_data <= 32'h0;
		o_DEN     <= 1'b0;
		o_DWE     <= 1'b0;
		o_DADDR   <= {(AW){1'b0}};
		o_DI      <= 16'b0;
		o_wb_ack  <= 1'b0;
		r_mask <= 16'h0;
		r_data <= 16'h0;
		// }}}
	end else case(fsm_state)
	DRP_IDLE: begin
		// {{{
		o_DEN   <= 1'b0;
		o_DWE   <= 1'b0;
		o_DADDR <= {(AW){1'b0}};
		o_DI    <= 16'h0;
		o_wb_ack <= 1'b0;
		r_mask <= 16'h0;
		r_data <= 16'h0;
		if (i_wb_stb && !o_wb_stall)
		begin
			o_DADDR <= i_wb_addr;
			r_mask <=  i_wb_data[31:16];
			r_data <=  i_wb_data[15: 0] & (~i_wb_data[31:16]);
			if (!(&i_wb_sel))
			begin
				o_wb_ack <= 1'b1;
				fsm_state <= DRP_IDLE;
			end else if (!i_wb_we)
			begin
				fsm_state <= DRP_READ;
				o_DEN <= 1'b1;
			end else begin // if (i_wb_we)
				fsm_state <= DRP_AND;
				o_DEN <= 1'b1;
			end
		end end
		// }}}
	DRP_READ: begin
		// {{{
		o_DEN <= 1'b1;
		o_DWE <= 1'b0;
		o_wb_ack <= 1'b0;
		if (i_DRDY)
		begin
			o_wb_ack  <= i_wb_cyc && r_will_ack;
			o_wb_data <= { 16'h0, i_DO };
			fsm_state <= DRP_IDLE;
			o_DEN <= 1'b0;
		end end
		// }}}
	DRP_AND: begin
		// {{{
		o_DEN <= 1'b1;
		o_DWE <= 1'b0;
		o_wb_ack <= 1'b0;
		if (i_DRDY)
		begin
			o_DI  <= (i_DO & r_mask) | r_data;
			fsm_state <= DRP_WRITE;
			o_DEN <= 1'b0;
			o_DWE <= 1'b1;
		end end
		//}}}
	DRP_WRITE: begin
		// {{{
		o_DEN <= 1'b1;
		o_DWE <= 1'b1;
		o_wb_ack <= 1'b0;
		if (o_DEN && i_DRDY)
		begin
			o_DEN <= 1'b0;
			o_DWE <= 1'b0;
			fsm_state <= DRP_IDLE;
			o_wb_ack  <= i_wb_cyc && r_will_ack;
		end end
		//}}}
	/*
	default: begin
		fsm_state <= DRP_IDLE;
		o_DEN <= 1'b0;
		o_DWE  <= 1'b0;
		end
	*/
	endcase

	assign	o_wb_stall = (fsm_state != DRP_IDLE);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// ILA Debug output
	// {{{
	always @(posedge i_clk)
	begin
		o_debug <= 0;

		o_debug[16 +: AW] <= o_DADDR;

		o_debug[31] <= i_wb_stb && !o_wb_stall;
		o_debug[30:29] <= fsm_state;
		o_debug[28] <= &i_wb_sel;
		o_debug[27] <= i_wb_cyc;
		o_debug[26] <= i_wb_stb;
		o_debug[25] <= i_wb_we;
		o_debug[24] <= o_wb_stall;
		o_debug[23] <= o_wb_ack;
		o_debug[22] <= o_DEN;
		o_debug[21] <= o_DWE;
		o_debug[20] <= i_DRDY;
		if (o_DWE)
			o_debug[15:0] <= o_DI;
		else
			o_debug[15:0] <= i_DO;
	end
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
`ifdef	FORMAL
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
	localparam	F_LGDEPTH=4;
	reg	f_past_valid;
	wire	[F_LGDEPTH-1:0]	fwb_nreq, fwb_nout, fwb_nack;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	fwb_slave #(
		.AW(AW), .F_LGDEPTH(F_LGDEPTH)
	) fwb (
		// {{{
		.i_clk(i_clk), .i_reset(i_reset),
		.i_wb_cyc(i_wb_cyc),
		.i_wb_stb(i_wb_stb),
		.i_wb_we(i_wb_we),
		.i_wb_addr(i_wb_addr),
		.i_wb_data(i_wb_data),
		.i_wb_sel(i_wb_sel),
		//
		.i_wb_ack(o_wb_ack),
		.i_wb_stall(o_wb_stall),
		.i_wb_idata(o_wb_data),
		.i_wb_err(1'b0),
		//
		.f_nreqs(fwb_nreq),
		.f_nacks(fwb_nack),
		.f_outstanding(fwb_nout)
		// }}}
	);

	always @(*)
	if (i_wb_cyc)
		assert(fwb_nout == ((o_wb_ack || r_will_ack) ? 1:0));

	always @(*)
	if (f_past_valid && fsm_state == DRP_IDLE)
		assert(o_wb_ack == r_will_ack);

	always @(*)
	if (f_past_valid && fsm_state != DRP_IDLE)
		assert(!o_wb_ack);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(o_DEN && !i_DRDY))
	begin
		assert(o_DEN);
		assert($stable(o_DWE));
		assert($stable(o_DADDR));
		assert($stable(o_DI));
	end
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checking
	// {{{
	reg	cvr_read, cvr_write;

	initial	cvr_read = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc || o_wb_ack)
		cvr_read <= 1'b0;
	else if (i_wb_stb && !o_wb_stall && !i_wb_we && (&i_wb_sel))
		cvr_read <= 1'b1;

	always @(*)
	if (!r_will_ack)
		assert(!cvr_read);

	initial	cvr_write = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_wb_cyc || o_wb_ack)
		cvr_write <= 1'b0;
	else if (i_wb_stb && !o_wb_stall && i_wb_we && (&i_wb_sel))
		cvr_write <= 1'b1;

	always @(*)
	if (!r_will_ack)
		assert(!cvr_write);

	always @(*)
		assert(!cvr_write || !cvr_read);

	always @(posedge i_clk)
	if (!i_reset && i_wb_cyc && o_wb_ack)
	begin
		cover(cvr_read);
		cover(cvr_write);
	end
	// }}}
`endif
// }}}
endmodule
