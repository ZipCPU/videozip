////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addepreamble.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To add the ethernet preamble to a stream of values (i.e., to
//		an ethernet packet ...)
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
module addepreamble(i_clk, i_reset, i_ce, i_en, i_v, i_d, o_v, o_d);
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire		i_v;	// Valid
	input	wire	[7:0]	i_d;	// Data Byte
	output	reg		o_v;
	output	reg	[7:0]	o_d;

	reg	[8*9-1:0]	shiftreg;

	initial	o_v = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_v <= 1'b0;
		o_d <= 8'h0;
		shiftreg <= {
			9'h155, 9'h155, 9'h155, 9'h155,
			9'h155, 9'h155, 9'h155, 9'h15d };
	end else if (i_ce) begin
		shiftreg <= { shiftreg[62:0], { i_v, i_d }};
		o_v <= shiftreg[71]&&((o_v)||(i_v));
		o_d <= shiftreg[70:63];
		if ((!i_v)&&(!o_v))
		begin
			shiftreg <= {
				9'h155, 9'h155, 9'h155, 9'h155,
				9'h155, 9'h155, 9'h155, 9'h15d };
			if (!i_en)
			begin
				shiftreg[1*9-1] <= 1'b0;
				shiftreg[2*9-1] <= 1'b0;
				shiftreg[3*9-1] <= 1'b0;
				shiftreg[4*9-1] <= 1'b0;
				shiftreg[5*9-1] <= 1'b0;
				shiftreg[6*9-1] <= 1'b0;
				shiftreg[7*9-1] <= 1'b0;
				shiftreg[8*9-1] <= 1'b0;
			end
		end
	end

`ifdef	FORMAL
	reg	[9-1:0]		f_v;
	reg	[9*8-1:0]	f_d;
	reg	[3:0]		f_cnt;
	reg			f_past_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if (!$past(i_ce))
	begin
		assume($stable(i_en));
		assume($stable(i_v));
		assume($stable(i_d));
	end
	
	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||(o_v))&&(!$past(i_reset)))
		assume($stable(i_en));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_v))&&(!$past(i_v)))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(i_v))
		assume($stable(i_en));

	initial	f_cnt = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cnt <= 0;
	else if (i_ce)
	begin
		if (!i_v)
			f_cnt <= 0;
		else if (! &f_cnt)
			f_cnt <= f_cnt + 1'b1;
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_v))&&(f_cnt < 9))
		assume(i_v);

	////////////////////////////////////////////////////////////////////////
	//
	//

	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[9-1:0], i_v };

	always @(posedge i_clk)
	if (i_ce)
		f_d <= { f_d[8*9-1:0], i_d };

	always @(posedge i_clk)
	if ((f_past_valid)
		&&($past(f_past_valid))
		&&(o_v)&&(f_cnt > 8))
	begin
		assert(o_v == f_v[8]);
		assert(o_d == f_d[8*9-1:8*8]);
 		// Was { o_v, o_d } == $past({ i_v, i_d }, 9));
	end

	always @(posedge i_clk)
	if (i_en && i_v && (&f_v[1:0]))
		assert(o_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(i_v)&&(f_cnt < 9)&&(i_en))
	case (f_cnt)
	4'h1: assert((o_v)&&(o_d == 8'h55));
	4'h2: assert((o_v)&&(o_d == 8'h55));
	4'h3: assert((o_v)&&(o_d == 8'h55));
	4'h4: assert((o_v)&&(o_d == 8'h55));
	4'h5: assert((o_v)&&(o_d == 8'h55));
	4'h6: assert((o_v)&&(o_d == 8'h55));
	4'h7: assert((o_v)&&(o_d == 8'h55));
	4'h8: assert((o_v)&&(o_d == 8'h5d));
	endcase
	else if ((f_past_valid)&&(f_cnt < 4'h9)&&(f_v[0]))
		assert(!o_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(o_v)&&(f_cnt >= 9))
		assert(o_d == f_d[9*8-1:8*8]);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
		cover($fell(o_v));
`endif
endmodule
