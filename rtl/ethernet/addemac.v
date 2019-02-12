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
module	addemac(i_clk, i_reset, i_ce, i_en, i_hw_mac,
		i_v, i_byte, o_v, o_byte);
	input	wire		i_clk, i_reset, i_ce, i_en;
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
		r_buf <= {(6){ 1'b0, 8'h55 } };
		r_pos <= 0;
		o_v   <= 0;
		o_byte<= 8'h55;
	end else if (i_ce) begin
		r_buf <= { r_buf[44:0], i_v, (i_v) ? i_byte : 8'hff };

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
		else if (!(&r_pos))
			r_pos <= r_pos + 5'h1;

		o_byte <= i_byte;

		if (i_en)
		begin

			if ((!i_v)&&(!o_v))
			begin
				o_v <= 1'b0;
			end else begin
				if (r_pos < 5'h6) // six bytes
					o_v <= i_v;
				else if (r_pos < 5'hc)	// 12 bytes
					o_v <= 1'b1;
				else
					o_v <= r_buf[53];
			end

			if (r_pos < 5'h6)
				o_byte <= i_byte;
			else if (r_pos < 5'hc)
				o_byte <= r_hw[47:40];
			else
				o_byte <= r_buf[52:45];
		end else
			o_v <= i_v;
	end

`ifdef	FORMAL
	reg			f_past_valid;
	reg	[7-1:0]		f_v;
	reg	[8*7-1:0]	f_d;

	initial	f_past_valid = 1'b0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	initial	assume(!i_v);

	always @(posedge i_clk)
	if ($past(i_reset))
		assume(!i_v);

	// CE's will come fairly often, but may not necessarily be every clock
	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	// H/W MAC will never change mid-packet
	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||(o_v)))
	begin
		assume($stable(i_hw_mac));
		assume($stable(i_en));
	end

	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 1'b0;
	else if (i_ce)
		f_v <= { f_v[5:0], i_v };

	//
	// New packets will never start while the last is still active
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_v))&&(!f_v[0]))
		assume(!i_v);
	always @(posedge i_clk)
	if (!$past(i_ce))
		assume($stable(i_v));

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||(o_v)))
		assume(i_en == $past(i_en));

	reg	[3:0]	f_cnt;

	initial	f_cnt = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_cnt <= 0;
	else if (i_ce)
	begin
		if (!o_v)
			f_cnt <= 0;
		else if (! &f_cnt)
			f_cnt <= f_cnt + 1'b1;
	end

	initial	f_d = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_d <= 0;
	else if (i_ce)
		f_d <= { f_d[8*7-1 : 0], i_byte };

	always @(posedge i_clk)
	if ((f_past_valid)&&(f_v[0] ||($past(f_cnt) > 0))
			&&($past(f_cnt) < 12)&&(!$past(i_reset)))
		assume(i_v);

	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(*)
	if ((r_pos > 0)&&(!r_pos[4]))
		assert(f_cnt == r_pos-1);
	else if ((r_pos[4])&&(r_pos[3:0] != 0))
		assert(&f_cnt);
	else if (r_pos == 0)
		assert(f_cnt == 0);


	always @(posedge i_clk)
	if (f_v[0])
	begin
		case(f_cnt)
		4'h0: assert(r_hw == { i_hw_mac[39:0], i_hw_mac[47:40] });
		4'h1: assert(r_hw == { i_hw_mac[31:0], i_hw_mac[47:32] });
		4'h2: assert(r_hw == { i_hw_mac[23:0], i_hw_mac[47:24] });
		4'h3: assert(r_hw == { i_hw_mac[15:0], i_hw_mac[47:16] });
		4'h4: assert(r_hw == { i_hw_mac[ 7:0], i_hw_mac[47: 8] });
		4'h5: assert(r_hw == i_hw_mac);
		4'h6: assert(r_hw == { i_hw_mac[39:0], i_hw_mac[47:40] });
		4'h7: assert(r_hw == { i_hw_mac[31:0], i_hw_mac[47:32] });
		4'h8: assert(r_hw == { i_hw_mac[23:0], i_hw_mac[47:24] });
		4'h9: assert(r_hw == { i_hw_mac[15:0], i_hw_mac[47:16] });
		4'ha: assert(r_hw == { i_hw_mac[ 7:0], i_hw_mac[47: 8] });
		4'hb: assert(r_hw == i_hw_mac);
		4'hc: assert(r_hw == { i_hw_mac[39:0], i_hw_mac[47:40] });
		4'hd: assert(r_hw == { i_hw_mac[31:0], i_hw_mac[47:32] });
		default: begin end
		endcase
	end

	always @(posedge i_clk)
	if ((o_v)&&(i_en))
	begin
		case(f_cnt)
		4'h0: assert(o_byte == f_d[7:0]);
		4'h1: assert(o_byte == f_d[7:0]);
		4'h2: assert(o_byte == f_d[7:0]);
		4'h3: assert(o_byte == f_d[7:0]);
		4'h4: assert(o_byte == f_d[7:0]);
		4'h5: assert(o_byte == f_d[7:0]);
		4'h6: assert(o_byte == i_hw_mac[47:40]);
		4'h7: assert(o_byte == i_hw_mac[39:32]);
		4'h8: assert(o_byte == i_hw_mac[31:24]);
		4'h9: assert(o_byte == i_hw_mac[23:16]);
		4'ha: assert(o_byte == i_hw_mac[15: 8]);
		4'hb: assert(o_byte == i_hw_mac[ 7: 0]);
		default: begin
			assert(o_byte == f_d[8*6 +: 8]);
		end endcase
	end else if ((o_v)&&(!i_en))
		assert(o_byte == f_d[7:0]);

	always @(posedge i_clk)
	begin
		/*
		assert((f_v == 7'h00)||(f_v == 7'h01)
			||(f_v == 7'h03)||(f_v == 7'h07)
			||(f_v == 7'h0f)||(f_v == 7'h1f)
			||(f_v == 7'h3f)||(f_v == 7'h7f)
			||(f_v == 7'h7e)||(f_v == 7'h7c)
			||(f_v == 7'h78)||(f_v == 7'h70)
			||(f_v == 7'h60)||(f_v == 7'h40));
		*/

		casez(f_v)
		7'b000_0001: assert(r_pos == 1);
		7'b000_0011: assert(r_pos == 2);
		7'b000_0111: assert(r_pos == 3);
		7'b000_1111: assert(r_pos == 4);
		7'b001_1111: assert(r_pos == 5);
		7'b011_1111: assert(r_pos == 6);
		default: begin end
		endcase
	end

	always @(posedge i_clk)
	begin
		assert(!r_buf[ 8] || f_v[0]);
		assert(!r_buf[17] || f_v[1]);
		assert(!r_buf[26] || f_v[2]);
		assert(!r_buf[35] || f_v[3]);
		assert(!r_buf[44] || f_v[4]);
		assert(!r_buf[53] || f_v[5]);

		assert(r_buf[ 7: 0] == f_d[ 7: 0]);
		assert(r_buf[16: 9] == f_d[15: 8]);
		assert(r_buf[25:18] == f_d[23:16]);
		assert(r_buf[34:27] == f_d[31:24]);
		assert(r_buf[43:36] == f_d[39:32]);
		assert(r_buf[52:45] == f_d[47:40]);
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_en))
		assert((!o_v)||(o_byte == f_d[7:0]));
	always @(posedge i_clk)
	if ((f_past_valid)&&(!i_en)&&(!$past(i_reset)))
		assert(o_v == f_v[0]);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset)))
		cover($fell(o_v));
`endif
endmodule
