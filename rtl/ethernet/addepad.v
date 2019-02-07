////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addepad.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To force the minimum packet size of an ethernet frame to be
//		a minimum of 64 bytes.  This assumes that the CRC will be
//	adding 32-bits to the packet after us, so instead of padding to
//	64 bytes, we'll pad to 60 bytes instead.  If the user is providing
//	their own CRC, they'll need to adjust the padding themselves.
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
module addepad(i_clk, i_reset, i_ce, i_v, i_d, o_v, o_d);
	parameter	MINOCTETS=60;
	localparam	LGNCOUNT=(MINOCTETS<63)? 6
				:((MINOCTETS<127)? 7:((MINOCTETS<255)? 8:9));
	input	wire		i_clk, i_reset, i_ce;
	input	wire		i_v;	// Valid
	input	wire	[7:0]	i_d;	// Data nibble
	output	reg		o_v;
	output	reg	[7:0]	o_d;

	reg	[(LGNCOUNT-1):0]	r_ncnt;
	initial	o_v = 1'b0;
	initial	r_ncnt = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_ncnt <= 0;
		o_v <= 1'b0;
	end else if (i_ce)
	begin
		o_v <= (i_v)||((o_v)&&(r_ncnt<MINOCTETS-1'b1));

		if (!o_v)
			r_ncnt <= 0;
		else if (r_ncnt < MINOCTETS)
			r_ncnt <= r_ncnt + 1;
	end

	always @(posedge i_clk)
	if (i_reset)
		o_d <= 8'h00;
	else if (i_ce)
	begin
		if (i_v)
			o_d <= i_d;
		else
			o_d <= 8'h00;
	end

`ifdef	FORMAL
	reg	[LGNCOUNT-1:0]	f_count;
	reg			f_past_valid, f_v;
	reg	[7:0]		f_d;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Input assumptions
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	initial	assume(!i_v);
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_v))&&($past(o_v)))
		assume(!i_v);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(!$past(i_ce)))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end


	////////////////////////////////////////////////////////////////////////
	//
	// Assertions
	//
	initial	f_count = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_count <= 0;
	else if (i_ce)
	begin
		if (!o_v)
			f_count <= 0;
		else if (! &f_count)
			f_count <= f_count + 1'b1;
	end

	always @(posedge i_clk)
	if (i_reset)
		f_v <= 1'b0;
	else if (i_ce)
		f_v <= i_v;

	always @(posedge i_clk)
	if (i_ce)
		f_d <= i_d;

	always @(posedge i_clk)
	if (f_count != r_ncnt)
		assert((r_ncnt < f_count)&&(r_ncnt == MINOCTETS));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_v))&&(!$past(i_reset))&&(!o_v))
		assert(f_count >= MINOCTETS);

	always  @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(o_d == 0);
	else if ((f_past_valid)&&(f_v))
		assert(o_d == f_d);
	else if ((f_past_valid)&&(!f_v))
		assert(o_d == 0);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&(f_v))
		assert(o_v);


	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assert(!o_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover
	//
	reg	short_packet;

	initial short_packet = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		short_packet <= 1'b0;
	else if (($fell(i_v))&&(r_ncnt == 32))
		short_packet <= 1'b1;

	always @(posedge i_clk)
		cover(short_packet && $fell(o_v));

`endif
endmodule
