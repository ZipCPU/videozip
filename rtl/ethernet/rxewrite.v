////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxewrite.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	The purpose of this module is quite simple: to simplify the
//		receive process.  By running the receive data through a 
//	series of "filter" processes (of which this is one), I hope to reduce
//	the complexity of the filter design.  This particular filter determines
//	if/when to write to memory, and at what address to write to.  Further,
//	because nibbles come into the interface in LSB order, and because we
//	are storing the first byte in the MSB, we need to shuffle bytes around
//	in this interface.  Therefore, this interface is also design to make
//	certain that, no matter how many bytes come in, we have always 
//	written a complete word to the output.  Hence, each word may be
//	written 8-times (once for each nibble) ... but that be as it may.
//
//	This routine also measures packet length in bytes.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2019, Gisselquist Technology, LLC
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
module	rxewrite(i_clk, i_reset, i_ce, i_v, i_d, o_v, o_addr, o_data, o_len);
	parameter	AW = 12;
	localparam	DW = 32;
	input	wire			i_clk, i_reset, i_ce;
	input	wire			i_v;
	input	wire	[7:0]		i_d;
	output	reg			o_v;
	output	reg	[(AW-1):0]	o_addr;
	output	reg	[(DW-1):0]	o_data;
	output	wire	[(AW+1):0]	o_len;

	reg	[(AW+2):0]	lcl_addr;

	initial	o_v      = 0;
	initial	lcl_addr = 0;
	initial	o_data   = 0;
	initial	o_addr   = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_v      <= 0;
		lcl_addr <= 0;
		o_data   <= 0;
		o_addr   <= 0;
	end else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
		begin
			o_v      <= 0;
			lcl_addr <= 0;
			o_data   <= 0;
			o_addr   <= 0;
		end else begin
			lcl_addr <= lcl_addr + 1'b1;
			o_v <= i_v;
			case(lcl_addr[1:0])
			2'b00: o_data <= { i_d, 24'h00 };
			2'b01: o_data <= { o_data[31:24], i_d, 16'h00 };
			2'b10: o_data <= { o_data[31:16], i_d, 8'h00 };
			2'b11: o_data <= { o_data[31: 8], i_d };
			endcase
			o_addr <= lcl_addr[(AW+1):2];
		end
	end

	assign	o_len  = lcl_addr[(AW+1):0];


`ifdef	FORMAL
	reg	[31:0]	f_d;
	reg	[3:0]	f_v;

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	//
	initial	assume(i_reset);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!f_v[0])&&(f_v[1]))
		assume(!i_v);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume($stable(i_v) && $stable(i_d));

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);


	////////////////////////////////////////////////////////////////////////
	//
	// Safety (assertion) properties
	//
	always @(posedge i_clk)
	if (i_ce)
		f_d <= { f_d[23:0], i_d };
	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[2:0], i_v };

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset))
		||($past(i_ce && !i_v && !o_v)) )
	begin
		assert(o_v      == 0);
		assert(lcl_addr == 0);
		assert(o_data   == 0);
		assert(o_addr   == 0);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
		assert(o_v == f_v[0]);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(!i_reset && i_v && i_ce)))
	begin
		assert(o_v);
		case(lcl_addr[1:0])
		2'b01: assert((o_data[31:24]==f_d[ 7:0])&&(o_data[23:0]==0));
		2'b10: assert((o_data[31:16]==f_d[15:0])&&(o_data[15:0]==0));
		2'b11: assert((o_data[31: 8]==f_d[23:0])&&(o_data[ 7:0]==0));
		2'b00: assert( o_data[31: 0]==f_d[31:0]);
		endcase
	end else if (o_v)
		assert($stable(lcl_addr) && $stable(o_data) && $stable(o_addr));

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	always @(posedge i_clk)
		cover(o_v&&(!i_v));
	always @(posedge i_clk)
		cover(o_v && lcl_addr == 0 && o_addr == 10);
`endif
endmodule

