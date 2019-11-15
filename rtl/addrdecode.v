////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addrdecode.v
//
// Project:	Pipelined Wishbone to AXI converter
//
// Purpose:	
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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
module	addrdecode(i_clk, i_reset, i_valid, o_stall, i_addr, i_data,
			o_valid, i_stall, o_decode, o_addr, o_data);
	parameter	NS=8;
	parameter	AW = 32, DW=32+32/8+1+1;
	parameter	[NS*AW-1:0]	SLAVE_ADDR = {
				{ 3'b111, {(AW-3){1'b0}}},
				{ 3'b110, {(AW-3){1'b0}}},
				{ 3'b101, {(AW-3){1'b0}}},
				{ 3'b100, {(AW-3){1'b0}}},
				{ 3'b011, {(AW-3){1'b0}}},
				{ 3'b010, {(AW-3){1'b0}}},
				{ 4'b0010, {(AW-4){1'b0}}},
				{ 4'b0000, {(AW-4){1'b0}}} };
	parameter	[NS*AW-1:0]	SLAVE_MASK = (NS <= 1) ? 0
		: { {(NS-2){ 3'b111, {(AW-3){1'b0}}}},
			{(2){ 4'b1111, {(AW-4){1'b0}} }} };
	parameter [0:0]	OPT_REGISTERED = 0;
	parameter [0:0]	OPT_LOWPOWER = 0;
	//
	input	wire			i_clk, i_reset;
	//
	input	wire			i_valid;
	output	reg			o_stall;
	input	wire	[AW-1:0]	i_addr;
	input	wire	[DW-1:0]	i_data;
	//
	output	reg			o_valid;
	input	wire			i_stall;
	output	reg	[NS:0]		o_decode;
	output	reg	[AW-1:0]	o_addr;
	output	reg	[DW-1:0]	o_data;

	reg	[NS:0]	request;
	reg		none_sel;
	integer		iM;

	always @(*)
	begin
		// Let's assume nothing's been selected, and then check
		// to prove ourselves wrong.
		//
		// Note that none_sel will be considered an error condition
		// in the follow-on processing.  Therefore it's important
		// to clear it if no request is pending.
		none_sel = i_valid;
		for(iM=0; iM<NS; iM=iM+1)
		begin
			if (((i_addr ^ SLAVE_ADDR[iM*AW +: AW])
					&SLAVE_MASK[iM*AW +: AW])==0)
				none_sel = 0;
		end
	end

	always @(*)
	begin
		for(iM=0; iM<NS; iM=iM+1)
			request[iM] = i_valid
				&&(((i_addr ^ SLAVE_ADDR[iM*AW +: AW])
					&SLAVE_MASK[iM*AW +: AW])==0);

		//
		// request[NS] indicates a request forr a non-existent
		// slave.  A request that should (eventually) return a bus
		// error
		//
		request[NS] = none_sel;
	end

	generate if (OPT_REGISTERED)
	begin
		initial	o_valid = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_valid <= 0;
		else if (!o_stall)
			o_valid <= i_valid;


		initial	o_addr   = 0;
		initial	o_data   = 0;
		always @(posedge i_clk)
		if (i_reset && OPT_LOWPOWER)
		begin
			o_addr   <= 0;
			o_data   <= 0;
		end else if ((!o_valid || !i_stall)
				 && (i_valid || !OPT_LOWPOWER))
		begin
			o_addr   <= i_addr;
			o_data   <= i_data;
		end else if (OPT_LOWPOWER && !i_stall)
		begin
			o_addr   <= 0;
			o_data   <= 0;
		end

		initial	o_decode = 0;
		always @(posedge i_clk)
		if (i_reset)
			o_decode <= 0;
		else if ((!o_valid || !i_stall)
				 && (i_valid || !OPT_LOWPOWER))
			o_decode <= request;
		else if (OPT_LOWPOWER && !i_stall)
			o_decode <= 0;

		always @(*)
			o_stall = (o_valid && i_stall);
	end else begin

		always @(*)
		begin
			o_valid = i_valid;
			o_stall = i_stall;
			o_addr  = i_addr;
			o_data  = i_data;

			o_decode = request;
		end

		// verilator lint_off UNUSED
		wire	unused;
		assign	unused = &{ 1'b0, i_clk, i_reset };
		// verilator lint_on UNUSED
	end endgenerate

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	reg	[AW+DW-1:0]	f_idata;
	always @(*)
		f_idata = { i_addr, i_data };

`ifdef	ADDRDECODE
	always @(posedge i_clk)
	if (!f_past_valid)
		assume(i_reset);

	/*
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_valid);
	else if ($past(i_valid && o_stall))
	begin
		assume(i_valid);
		// assume($stable(f_idata));
	end
	*/
`else
	always @(posedge i_clk)
	if (!f_past_valid)
		assert(i_reset);

/*
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!i_valid);
	else if ($past(i_valid && o_stall))
	begin
		assert(i_valid);
		// assert($stable(f_idata) || (!OPT_REGISTERED && i_reset));
	end
*/
`endif	// ADDRDECODE
	always @(posedge i_clk)
	if (OPT_REGISTERED && (!f_past_valid || $past(i_reset)))
	begin
		assert(!o_valid);
		assert(o_decode == 0);
	end else if ($past(o_valid && i_stall) && OPT_REGISTERED)
	begin
		assert($stable(o_addr));
		assert($stable(o_decode));
		assert($stable(o_data));
	end

	// If the output is ever valid, there must be at least one
	// decoded output
	always @(*)
		assert(o_valid == (o_decode != 0));

	always @(*)
	for(iM=0; iM<NS; iM=iM+1)
	if (o_decode[iM])
	begin
		// The address must match
		assert(((o_addr ^ SLAVE_ADDR[iM*AW +: AW])
				& SLAVE_MASK[iM*AW +: AW])==0);
		//
		// And nothing else must match
		assert(o_decode == (1<<iM));
	end

	generate if (OPT_LOWPOWER && OPT_REGISTERED)
	begin
		always @(*)
		if (!o_valid)
		begin
			assert(o_addr   == 0);
			assert(o_decode == 0);
			assert(o_data   == 0);
		end
	end endgenerate

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	// Make sure all addresses are reachable
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	[NS:0]	f_reached;

	always @(posedge i_clk)
		cover(i_valid);

	always @(posedge i_clk)
		cover(o_valid);

	always @(posedge i_clk)
		cover(o_valid && !i_stall);

	initial	f_reached = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_reached = 0;
	else if (o_valid)
		f_reached = f_reached | o_decode;

	generate if (SLAVE_MASK == 0 && NS == 1)
	begin
		
		always @(*)
			cover(f_reached[0]);

		always @(*)
			assert(!f_reached[NS]);

		always @(posedge i_clk)
		if (f_past_valid && $stable(o_valid))
			assert($stable(o_decode));

	end else begin

		always @(*)
			cover(&f_reached);

		always @(posedge i_clk)
		if (f_past_valid && $stable(o_valid))
			cover($changed(o_decode));

	end endgenerate

`endif	// FORMAL
endmodule
