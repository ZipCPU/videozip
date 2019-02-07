////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxepreambl.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To detect, and then remove, any ethernet hardware preamble.
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
module	rxepreambl(i_clk, i_reset, i_ce, i_en, i_v, i_d, o_v, o_d);
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;

	reg	r_inpkt;
	reg	[3:0]	nsyncs;

	initial	nsyncs  = 0;
	always @(posedge i_clk)
	if (i_reset)
		nsyncs <= 0;
	else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
			nsyncs <= 0;
		else if ((i_d == 8'h55)&&(i_v))
		begin
			if (! (&nsyncs))
				nsyncs <= nsyncs + 1'b1;
		end else
			nsyncs <= 0;
	end

	initial	o_v = 1'b0;
	initial	o_d = 8'h0;
	initial	r_inpkt = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_inpkt <= 1'b0;
		o_v     <= 1'b0;
		o_d     <= 8'h0;
	end else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
		begin
			// Soft reset
			//
			// Set us up for the next packet
			r_inpkt <= 1'b0;
			o_v <= 1'b0;
			o_d <= 8'h0;
		end else if (!r_inpkt)
		begin
			r_inpkt <= (nsyncs > 4'h6)&&(i_v)&&(i_d == 8'h5d);
			o_v <= 1'b0;
			o_d <= 8'h0;
		end else begin
			o_v <= (i_v);
			o_d <= (i_v) ? i_d : 8'h0;
		end

		if (!i_en)
		begin
			o_v <= i_v;
			o_d <= (i_v) ? i_d : 8'h0;
		end
	end

`ifdef	FORMAL
	reg	[6:0]	f_match;
	reg	[7:0]	f_d;
	reg		f_v;
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(posedge i_clk)
	if ((i_v)||(o_v))
		assume($stable(i_en));

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);
	else if (!$past(i_ce))
		assume($stable(i_v));

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if ($past(i_v || o_v))
		assume($stable(i_en));

	always @(posedge i_clk)
	if (!$past(i_ce))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end

	always @(posedge i_clk)
	if ((o_v)&&(!$past(i_v)))
		assume(!i_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Safety properties
	//
	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= i_v;

	initial	f_match = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_match <= 0;
	else if (i_ce)
	begin
		f_d <= i_d;
		if ((i_v)&&(i_d == 8'h55))
			f_match <= { f_match[5:0], (i_d == 8'h55) };
		else
			f_match <= 0;
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_v))
		assert(o_d == f_d[7:0]);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assert(!r_inpkt);
	else if (!$past(i_ce))
		assert($stable(r_inpkt));
	else if ($past(&f_match) && f_v && $past(nsyncs >= 6) && ($past(i_d) == 8'h5d))
		assert(r_inpkt);

	always @(posedge i_clk)
	if (o_v && i_en)
		assert(r_inpkt);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_en))&&(!$past(i_reset))
			&&($past(nsyncs>4'h6))&&(f_v)
			&&($past(i_d == 8'h5d))
			&&($past(i_ce)))
		assert(r_inpkt);
	else if ((f_past_valid)&&($past(i_en))&&(!$past(r_inpkt)))
		assert(!o_v);

	// always @(posedge i_clk)
	// if ((f_past_valid)&&(!$past(i_reset))&&($past(r_inpkt))&&(f_v))
	//	assert(o_v);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assert(!o_v);
	else if ((f_v)&&($past(o_v)))
		assert(o_v);
	else if ((f_v)&&($past(i_ce && !i_en)))
		assert(o_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_en)))
	begin
		if (o_v)
			assert(o_d == f_d);
		else
			assert(o_d == 8'h0);
	end

	always @(posedge i_clk)
	case(nsyncs)
	4'h0: assert(f_match == 0);
	4'h1: assert(f_match == 6'h01);
	4'h2: assert(f_match == 6'h03);
	4'h3: assert(f_match == 6'h07);
	4'h4: assert(f_match == 6'h0f);
	4'h5: assert(f_match == 6'h1f);
	default: begin end
	endcase

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	always @(posedge i_clk)
		cover(o_v);

	always @(posedge i_clk)
		cover(o_v && i_en);

`endif
endmodule

