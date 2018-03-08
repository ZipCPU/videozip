////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addemac.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To add the device hardware MAC address into a data stream
//		that doesn't have it.
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
module	addemac(i_clk, i_reset, i_en, i_hw_mac,
		i_v, i_byte, o_v, o_byte);
	input	wire		i_clk, i_reset, i_en;
	input	wire	[47:0]	i_hw_mac;
	input	wire		i_v;
	input	wire	[7:0]	i_byte;
	output	reg		o_v;
	output	reg	[7:0]	o_byte;

	reg	[47:0]		r_hw;
	reg	[((8+1)*6)-1:0]	r_buf;
	reg	[4:0]		r_pos;

	initial	r_buf  = 0;
	initial	r_pos  = 0;
	initial	o_v    = 0;
	initial	o_byte = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_hw  <= i_hw_mac;
		r_buf <= 0;
		r_pos <= 0;
		o_v   <= 0;
		o_byte<= 0;
	end else begin
		r_buf <= { r_buf[44:0], i_v, i_byte };

		if ((!i_v)&&(!o_v))
		begin
			r_buf[ 8] <= 1'b0;
			r_buf[17] <= 1'b0;
			r_buf[26] <= 1'b0;
			r_buf[35] <= 1'b0;
			r_buf[44] <= 1'b0;
			r_buf[53] <= 1'b0;
		end

		if (!i_v)
			r_hw <= i_hw_mac;
		else
			r_hw <= { r_hw[39:0], r_hw[47:40] };

		if ((!i_v)&&(!o_v))
			r_pos <= 5'h0;
		else if ((r_pos < 5'h0c )&&(i_en))
			r_pos <= r_pos + 5'h1;
		else if ((r_pos < 5'h10 )&&(!i_en))
			r_pos <= r_pos + 5'h1;

		if (i_en)
		begin
			if ((!i_v)&&(!o_v))
			begin
				o_v <= 1'b0;
			end else begin
				if (r_pos < 5'h6) // six bytes
				begin
					{ o_v, o_byte } <= { i_v, i_byte };
				end else if (r_pos < 5'hc)	// 12 bytes
				begin
					{ o_v, o_byte } <= { 1'b1, r_hw[47:40] };
				end else
					{ o_v, o_byte } <= r_buf[53:45];
			end
		end else
			{ o_v, o_byte } <= { i_v, i_byte };
		if(i_reset)
			o_v <= 1'b0;
	end
`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	initial	assume(!i_v);

	always @(posedge i_clk)
	if ($past(i_reset))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||(o_v)))
		assume(i_hw_mac == $past(i_hw_mac));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_v))&&(!$past(i_v)))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||(o_v)))
		assume(i_en == $past(i_en));

	reg	[3:0]	f_cnt;

	initial	f_cnt = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cnt <= 0;
	else if (!o_v)
		f_cnt <= 0;
	else if (! &f_cnt)
		f_cnt <= f_cnt + 1'b1;

	always @(posedge i_clk)
	if ((f_past_valid)&&(($past(i_v))||($past(f_cnt) > 0))&&($past(f_cnt) < 12)&&(!$past(i_reset)))
		assume(i_v);

	always @(posedge i_clk)
	if ((o_v)&&(i_en))
	begin
		case(f_cnt)
		4'h0: assert(o_byte == $past(i_byte));
		4'h1: assert(o_byte == $past(i_byte));
		4'h2: assert(o_byte == $past(i_byte));
		4'h3: assert(o_byte == $past(i_byte));
		4'h4: assert(o_byte == $past(i_byte));
		4'h5: assert(o_byte == $past(i_byte));
		4'h6: assert(o_byte == i_hw_mac[47:40]);
		4'h7: assert(o_byte == i_hw_mac[39:32]);
		4'h8: assert(o_byte == i_hw_mac[31:24]);
		4'h9: assert(o_byte == i_hw_mac[23:16]);
		4'ha: assert(o_byte == i_hw_mac[15: 8]);
		4'hb: assert(o_byte == i_hw_mac[ 7: 0]);
		default: begin
			assert((!f_past_valid)||(o_byte == $past(i_byte,7)));
		end endcase
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_en))
		assert((!o_v)||(o_byte == $past(i_byte)));
	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_en)&&(!$past(i_reset)))
		assert(o_v == $past(i_v));
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_v)))
		cover(!o_v);
`endif
endmodule
