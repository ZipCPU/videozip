////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	txeaddr.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To calculate and control the reading of the transmit buffer,
//		and to issue the results to the next stage of the transmit
//	processing pipeline.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
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
`default_nettype	none
//
module	txeaddr(i_clk, i_reset, i_ce,
		i_start, i_len, o_addr, i_data, o_memv, o_memd);
	parameter	LGNBYTES = 12;
	localparam	DW = 32;
	localparam	OW = 8;
	localparam	MINPKTSZ = 8;
	input	wire	i_clk, i_reset, i_ce;
	//
	input	wire			i_start;
	input	wire [LGNBYTES-1:0]	i_len;
	output	wire [LGNBYTES-3:0]	o_addr;
	input	wire	[DW-1:0]	i_data;
	//
	output	reg			o_memv;
	output	wire	[OW-1:0]	o_memd;
	//

	reg	[LGNBYTES:0]	r_len, lcl_addr, next_addr;
	reg	[DW-1:0]	data_reg;

	reg	start_signal;
	wire	w_ce;

	assign	w_ce = (i_ce && o_memv);

	initial	start_signal = 0;
	always @(posedge i_clk)
	if (i_reset)
		start_signal <= 0;
	else
		start_signal <= (i_start && !o_memv && !start_signal
			&& (i_len >= MINPKTSZ));

	initial	o_memv = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_memv <= 0;
	else if (start_signal)
		o_memv <= 1;
	else if (w_ce)
		o_memv <= (lcl_addr < r_len);

	initial	r_len = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_len <= 0;
	else if (i_start && !o_memv && !start_signal)
		r_len <= { 1'b0, i_len };

	// lcl_addr is defined to be one past the address of the data
	// currently being sent
	initial	lcl_addr  = 0;
	initial	next_addr = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		lcl_addr  <= 0;
		next_addr <= 1;
	end else if (start_signal)
	begin
		lcl_addr  <= 1;
		next_addr <= 2;
	end else if (w_ce)
	begin
		lcl_addr  <= lcl_addr + 1;
		next_addr <= lcl_addr + 2;
	end else if (!o_memv)
	begin
		lcl_addr  <= 0;
		next_addr <= 1;
	end

	assign	o_addr = next_addr[LGNBYTES-1:2];


	always @(posedge i_clk)
	if (o_memv && i_ce)
	begin
		if (!o_memv || lcl_addr[1:0] == 2'b00)
			data_reg <= i_data;
		else
			data_reg <= data_reg << 8;
	end else if (!o_memv)
		data_reg <= i_data;

	assign	o_memd = data_reg[31:24];

	// Make Verilator happy
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, next_addr[LGNBYTES], next_addr[1:0] };
	// Verilator lint_on  UNUSED
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our input(s)
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if (!f_past_valid)
		assume(!i_start);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	////////////////////////////////////////////////////////////////////////
	//
	// Contract:
	//
	// Given a particular memory address, the contents of that address
	// should be issued out one at a time over the course of four separate
	// clock periods
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg [LGNBYTES-3:0]	f_const_addr;
	(* anyconst *)	reg [DW-1:0]		f_const_data;
	reg	[3:0]	f_sent;

	always @(posedge i_clk)
	if ($past(o_addr) == f_const_addr)
		assume(i_data == f_const_data);

	always @(posedge i_clk)
	if ($past(o_memv))
		assume(!i_start);

	reg	[LGNBYTES-1:0]	f_last_addr;
	always @(*)
		f_last_addr = lcl_addr - 1;

	always @(*)
	if (o_memv && f_last_addr[LGNBYTES-1:2] == f_const_addr)
	begin
		case(f_last_addr[1:0])
		2'b00: assert(o_memd == f_const_data[31:24]);
		2'b01: assert(o_memd == f_const_data[23:16]);
		2'b10: assert(o_memd == f_const_data[15: 8]);
		2'b11: assert(o_memd == f_const_data[ 7: 0]);
		endcase
	end

	always @(posedge i_clk)
	if (i_reset || start_signal)
		f_sent <= 0;
	else if (i_ce && o_memv && f_last_addr[LGNBYTES-1:2] == f_const_addr)
	begin
		case(f_last_addr[1:0])
		2'b00: f_sent[0] <= (o_memd == f_const_data[31:24]);
		2'b01: f_sent[1] <= (o_memd == f_const_data[23:16]);
		2'b10: f_sent[2] <= (o_memd == f_const_data[15: 8]);
		2'b11: f_sent[3] <= (o_memd == f_const_data[ 7: 0]);
		endcase
	end

	always @(*)
	if (lcl_addr > { f_const_addr, 2'b00 } + 5)
		assert(&f_sent);

	////////////////////////////////////////////////////////////////////////
	//
	// Induction properties
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (o_memv)
		assert(lcl_addr <= r_len);

	always @(posedge i_clk)
	if (o_memv)
		assert(lcl_addr > 0);

	always @(*)
	if (o_memv)
	begin
		case(f_last_addr[1:0])
		2'b01: assert(data_reg[ 7:0] ==  8'h00);
		2'b10: assert(data_reg[15:0] == 16'h00);
		2'b11: assert(data_reg[23:0] == 24'h00);
		default: begin end
		endcase
	end

	always @(*)
		assert(next_addr - 1 == lcl_addr);
	always @(*)
		assert(r_len[LGNBYTES]==1'b0);
`endif
endmodule
