////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxehwmac.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To remove MACs that aren't our own.  The input is a byte stream,
//	where the first byte is the first byte of the destination MAC (our MAC).
//	If enabled, this MAC is removed from the stream.  If the MAC matches,
//	the stream is allowed to continue.  If the MAC doesn't match, the
//	packet is thrown away.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2018, Gisselquist Technology, LLC
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
module	rxehwmac(i_clk, i_reset, i_en, i_hwmac, i_v, i_d, o_v, o_d, o_err, o_broadcast);
	input	wire		i_clk, i_reset, i_en;
	input	wire	[47:0]	i_hwmac;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;
	output	reg		o_err;
	output	reg		o_broadcast;

	reg	[47:0]	r_hwmac;
	reg		r_hwmatch, r_broadcast;
	reg	[17:0]	r_buf;
	reg	[13:0]	r_p;

	always @(posedge i_clk)
	if (i_reset)
		r_hwmac <= i_hwmac;
	else if ((!i_v)&&(!o_v))
		r_hwmac <= i_hwmac;
	else if ((i_v)&&(r_p[5]))
		r_hwmac <= { r_hwmac[39:0], 8'h0 };

	initial	r_hwmatch   = 1'b1;
	initial	r_broadcast = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_hwmatch   <= 1'b1;
		r_broadcast <= 1'b1;
	end else if ((!i_v)&&(!o_v))
	begin
		r_hwmatch   <= 1'b1;
		r_broadcast <= 1'b1;
	end else if (r_p[5]) begin	// Up until 6-bytes have past
		if (r_hwmac[47:40] != i_d)
			r_hwmatch <= 1'b0;
		if (8'hff != i_d)
			r_broadcast<= 1'b0;
	end

	initial	o_broadcast = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_broadcast <= 1'b0;
	else if ((!r_p[5])&&(i_v))
		o_broadcast <= (r_broadcast);

	//
	// r_p
	//
	initial	r_p = 14'h3f_ff;
	always @(posedge i_clk)
	if (i_reset)
		r_p <= 14'h3f_ff;
	else if ((!i_v)&&(!o_v))
		r_p <= 14'h3f_ff;
	else
		r_p <= { r_p[12:0], 1'b0 };

	initial	r_buf = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_buf <= 0;
	else if ((!i_v)&&(!o_v))
		r_buf <= 0;
	else begin
		r_buf <= { r_buf[8:0], i_v, i_d };	/////

		if ((!i_en)&&(r_p[13]))
			r_buf[17:10] <= 8'h0;
	end

	initial	o_v = 1'b0;
	initial	o_d = 8'h0;
	always @(posedge i_clk)
	if (i_reset)
		{ o_v, o_d } <= { 1'b0, 8'h0 };
	else if ((!i_v)&&(!o_v))
		{ o_v, o_d } <= { 1'b0, 8'h0 };
	else if (i_en)
		// Skip the first 6 bytes, and everything
		// following if the MAC doesn't match
		{ o_v, o_d } <= { ((r_hwmatch)||(r_broadcast))&&(i_v), i_d };
	else if (r_p[13])
		// In this case, we wish to ignore everything,
		// but still duplicate the EtherType words
		{ o_v, o_d } <= { (i_v), i_d };
	else
		{ o_v, o_d } <= { r_buf[17], r_buf[16:9] };


	always @(posedge i_clk)
	if ((i_reset)||(!i_v))
		o_err <= 1'b0;
	else if ((i_en)&&(i_v))
		o_err <= (!r_hwmatch)&&(!r_broadcast);

`ifdef	FORMAL
	reg		f_past_valid;
	reg	[7:0]	f_v;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(!o_v);

	always @(posedge  i_clk)
	if ((f_past_valid)&&(i_v))
		assume(i_hwmac == $past(i_hwmac));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_err)))
		assume((i_reset)&&(!i_v));

	always @(posedge i_clk)
	if ((f_past_valid)&&(($past(i_v))||($past(o_v))))
		assume(i_en == $past(i_en));

	initial	assume(!i_v);
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else
		f_v <= { f_v[6:0], i_v };

	always @(posedge i_clk)
	if ((f_past_valid)&&(|f_v)&&(! &f_v))
		assume(i_v == $past(i_v));

	initial	f_v = 0;
	always @(posedge i_clk)
		assert(	(f_v == 0)||(f_v == 8'h01)
			||(f_v == 8'h03) ||(f_v == 8'h07)
			||(f_v == 8'h0f) ||(f_v == 8'h1f)
			||(f_v == 8'h3f) ||(f_v == 8'h7f)
			||(f_v == 8'hff) ||(f_v == 8'hfe)
			||(f_v == 8'hfc) ||(f_v == 8'hf8)
			||(f_v == 8'hf0) ||(f_v == 8'he0)
			||(f_v == 8'hc0) ||(f_v == 8'h80));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(!o_v);
	else if ((f_v[7:1] == 7'h3f)&&($past(i_v,2))
			&&($past(i_d,2)==i_hwmac[7:0])
			&&($past(i_d,3)==i_hwmac[15:8])
			&&($past(i_d,4)==i_hwmac[23:16])
			&&($past(i_d,5)==i_hwmac[31:24])
			&&($past(i_d,6)==i_hwmac[39:32])
			&&($past(i_d,7)==i_hwmac[47:40]))
		assert((o_v)&&(r_hwmatch));
	else if ((f_v[7:1] == 7'h3f)&&($past(i_v,2))
			&&($past(i_d,2)==8'hff)
			&&($past(i_d,3)==8'hff)
			&&($past(i_d,4)==8'hff)
			&&($past(i_d,5)==8'hff)
			&&($past(i_d,6)==8'hff)
			&&($past(i_d,7)==8'hff))
		assert((o_v)&&(r_broadcast));
	else if ((f_v == 8'h7f)&&($past(i_v)))
	begin
		assert((!o_v)||(!i_en));
		assert(!r_hwmatch);
		assert(!r_broadcast);
	end
	//else if ((f_past_valid)&&(!i_en)&&(!$past(i_en)))
	//	assert(o_v == $past(i_v));

	always @(posedge i_clk)
		cover((o_v)&&(r_hwmatch));

	always @(posedge i_clk)
		cover((o_v)&&(r_broadcast));

`endif
endmodule
