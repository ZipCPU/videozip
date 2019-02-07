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
module	rxehwmac(i_clk, i_reset, i_ce, i_en, i_hwmac, i_v, i_d, o_v, o_d, o_err, o_broadcast);
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire	[47:0]	i_hwmac;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;
	output	reg		o_err;
	output	reg		o_broadcast;

	reg	[47:0]	r_hwmac;
	reg		r_hwmatch, r_broadcast;
	reg	[6:0]	r_p;

	always @(posedge i_clk)
	if (i_reset)
		r_hwmac <= i_hwmac;
	else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
			r_hwmac <= i_hwmac;
		else if ((i_v)&&(r_p[5]))
			r_hwmac <= { r_hwmac[39:0], 8'h0 };
	end

	initial	r_hwmatch   = 1'b1;
	initial	r_broadcast = 1'b1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_hwmatch   <= 1'b1;
		r_broadcast <= 1'b1;
	end else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
		begin
			r_hwmatch   <= 1'b1;
			r_broadcast <= 1'b1;
		end else if (r_p[5]) begin	// Up until 6-bytes have past
			if (r_hwmac[47:40] != i_d)
				r_hwmatch <= 1'b0;
			if (8'hff != i_d)
				r_broadcast<= 1'b0;
		end
	end

	initial	o_broadcast = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_broadcast <= 1'b0;
	else if (i_ce)
	begin
		if (!i_v)
			o_broadcast <= 1'b0;
		else if (!r_p[5])
			o_broadcast <= (r_broadcast);
	end

	//
	// r_p
	//
	initial	r_p = -1;
	always @(posedge i_clk)
	if (i_reset)
		r_p <= -1;
	else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
			r_p <= -1;
		else
			r_p <= { r_p[5:0], 1'b0 };
	end

	initial	o_v = 1'b0;
	initial	o_d = 8'h0;
	always @(posedge i_clk)
	if (i_reset)
		{ o_v, o_d } <= { 1'b0, 8'h0 };
	else if (i_ce)
	begin
		o_v <= i_v;
		o_d <= i_d;

		if ((i_en)&&(r_p[5]))
			o_v <= 1'b0;
	end


	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else if (i_ce)
	begin
		if (!i_v)
			o_err <= 1'b0;
		else if ((i_en)&&(r_p[6:5]==2'b10)&&(i_v))
			o_err <= (!r_hwmatch)&&(!r_broadcast);
	end

`ifdef	FORMAL
`ifdef	RXEHWMAC
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg			f_past_valid;
	reg	[12:0]		f_v;
	reg	[8*8-1:0]	f_past_data;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Input assumptions
	//
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_ce)))
		`ASSUME(i_ce);

	always @(posedge  i_clk)
	if ((f_past_valid)&&(i_v))
		`ASSUME(i_hwmac == $past(i_hwmac));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_err)))
		`ASSUME((i_reset)&&(!i_v));

	always @(posedge i_clk)
	if ((f_past_valid)&&(($past(i_v))||($past(o_v))))
		`ASSUME(i_en == $past(i_en));

	initial	assume(!i_v);
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		`ASSUME(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&( ((|f_v)&&(! &f_v)) || (!$past(i_ce))))
		`ASSUME($stable(i_v));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_ce))&&(i_v))
		`ASSUME($stable(i_d));

	////////////////////////////////////////////////////////////////////////
	//
	// Assertions
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_reset)))
		assert(!o_v);

	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[11:0], i_v };

	always @(posedge i_clk)
	if (i_ce)
		f_past_data <= { f_past_data[7*8-1:0], i_d };

	always @(posedge i_clk)
		assert(	(f_v == 0)||(f_v == 13'h01)
			||(f_v == 13'h0003) ||(f_v == 13'h0007)
			||(f_v == 13'h000f) ||(f_v == 13'h001f)
			||(f_v == 13'h003f) ||(f_v == 13'h007f)
			||(f_v == 13'h00ff) ||(f_v == 13'h01ff)
			||(f_v == 13'h03ff) ||(f_v == 13'h07ff)
			||(f_v == 13'h0fff) ||(f_v == 13'h1fff)
			||(f_v == 13'h1ffe) ||(f_v == 13'h1ffc)
			||(f_v == 13'h1ff8) ||(f_v == 13'h1ff0)
			||(f_v == 13'h1fe0) ||(f_v == 13'h1fc0)
			||(f_v == 13'h1f80) ||(f_v == 13'h1f00)
			||(f_v == 13'h1e00) ||(f_v == 13'h1c00)
			||(f_v == 13'h1800) ||(f_v == 13'h1000));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
	begin
		if ((f_v[12:6] == 0)&&(|f_v[5:0])&&(i_en))
			assert(!o_v);
		else if (|f_v)
			assert(o_v == f_v[0]);
		else
			assert(!o_v);
	end

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_err);
		assert(!o_broadcast);
	end else if (!i_en)
	begin
		assert(!o_err);
	end else if (f_v[8:0] == 9'h07f)
	begin
		if (&f_past_data[55:8])
			assert((o_v)&&(r_broadcast)&&(!o_err)&&(o_broadcast));
		else if ((f_past_data[15:8]==i_hwmac[ 7: 0])
			&&(f_past_data[23:16]==i_hwmac[15: 8])
			&&(f_past_data[31:24]==i_hwmac[23:16])
			&&(f_past_data[39:32]==i_hwmac[31:24])
			&&(f_past_data[47:40]==i_hwmac[39:32])
			&&(f_past_data[55:48]==i_hwmac[47:40]))
			assert((o_v)&&(r_hwmatch)&&(!o_err)&&(!o_broadcast));
		else
			assert(o_v && o_err && !o_broadcast);
	end else if (!f_v[7])
	begin
		// Don't assert err until the header has been received
		assert(!o_err);
		assert(!o_broadcast);
	end else if (o_v)
	begin
		// Otherwise, during the packet, o_err should be stable
		assert($stable(o_err));
		assert($stable(o_broadcast));
	end else begin
		// Once the packet is complete, o_err should be de-asserted
		assert(!o_err);
		assert(!o_broadcast);
	end

	always @(*)
	if (!o_v)
	begin
		assert(!o_broadcast);
		assert(!o_err);
	end

	always @(*)
	if (o_err)
		assert(!o_broadcast);

	always @(posedge i_clk)
	if (o_v)
	begin
		// if ((i_en)&&(!f_v[12]))
			assert(o_d == f_past_data[7:0]);
		// else
			// assert(o_d == f_past_data[7:0]);
	end

	////////////////////////////////////////////////////////////////////////
	//
	//	Cover properties
	//
	always @(posedge i_clk)
		cover((o_v)&&(i_en)&&(r_hwmatch));

	always @(posedge i_clk)
		cover((o_v)&&(i_en)&&(r_broadcast));

	always @(posedge i_clk)
		cover((o_v)&&(o_err));

	always @(posedge i_clk)
		cover((o_v)&&(o_broadcast));

	always @(posedge i_clk)
		cover((o_v)&&(i_en)&&(!o_err)&&(!o_broadcast)&&(&f_v[9:0]));

`endif
endmodule
