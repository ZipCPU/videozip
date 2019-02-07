////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxeipchk.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To cull any IP packets (EtherType=0x0806) from the stream
//		whose packet header checksums don't match.
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
module rxeipchk(i_clk, i_reset, i_ce, i_en, i_v, i_d, o_err);
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire		i_v;	// Valid
	input	wire	[7:0]	i_d;	// Data nibble
	output	reg		o_err;

	reg		r_v;
	reg	[15:0]	r_word;
	reg	[6:0]	r_cnt;
	reg	[5:0]	r_idx;

	initial	r_cnt = 0;
	initial	r_idx = 0;
	initial	r_v   = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_cnt <= 0;
		r_idx <= 0;
		r_v   <= 0;
	end else if (i_ce)
	begin
		if (!i_v)
		begin
			r_cnt <= 0;
			r_idx <= 0;
			r_v   <= 0;
		end else
		begin
			if (!(&r_cnt))
				r_cnt <= r_cnt + 1'b1;
			if (&r_cnt)
				r_v <= 1'b0;
			else
				r_v <= (r_cnt[0]);
			r_idx[5:0] <= r_cnt[6:1];
			r_word <= { r_word[7:0], i_d };
		end
	end

	reg		r_ip;
	reg	[5:0]	r_hlen;
	reg	[16:0]	r_check;
	initial	o_err   = 0;
	initial	r_check = 0;
	initial	r_ip    = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_err   <= 0;
		r_check <= 0;
		r_ip    <= 0;
		r_hlen  <= 0;
	end else if (i_ce)
	begin
		if (!i_v)
		begin
			o_err   <= 0;
			r_check <= 0;
			r_ip    <= 0;
			r_hlen  <= 0;
		end else if (r_v) begin
			// Process 16'b words here
			if (r_idx == 6'h6)
				// Is this actually an IP packet?
				// Check the ethertype field
				r_ip <= (r_word == 16'h0800);
			else if ((r_ip)&&(r_idx == 6'h7))
				// Is this actually an IP packet?
				// Check the IP protocol version, make sure we
				// are ipv4
				r_ip <= ((r_word[15:12] == 4'h4)
						&&(r_word[11:8] >= 4'h5));
			// else if (r_idx == r_hlen)
			//	r_ip <= 1'b0;
			if (r_idx == 6'h7)
				r_hlen <= {r_word[11:8], 1'b0 } + 5'h7;
			if (r_idx == 6'h7)
				// It's an error if we aren't an IPv4 packet
				//  ... or being an IPv4 packet if the length
				// isn't at least 5 words
				o_err <= (r_ip)&&(i_en)
					&&((r_word[15:12] != 4'h4)
					||(r_word[11:8] < 4'h5));
			if ((r_idx > 6'h8)&&(r_idx == r_hlen))
				o_err <= (o_err) || ((r_ip)&&(i_en)&&
					((r_check[15:1] != 15'h7fff)
					||((r_check[0]^r_check[16])!=1'b1)));
			if (r_ip)
				r_check <= r_check[15:0] + r_word + { 15'h0, r_check[16]};
		end
	end

`ifdef	FORMAL
	reg		f_past_valid;
	reg	[15:0]	f_bytecount;
	reg	[23:0]	f_d;
	reg	[2:0]	f_v;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	initial	assume(!i_v);
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||($past(i_v))))
		assume($stable(i_en));

	initial	f_bytecount = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_bytecount <= 0;
	else if (i_ce)
	begin
		if (!i_v)
			f_bytecount <= 0;
		else
			f_bytecount <= f_bytecount + 1'b1;
	end

	always @(posedge i_clk)
	if (f_bytecount > 16'd32760)
		assume(!i_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Safety properties / assumptions
	//
	initial	f_v = 0;
	always @(posedge  i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[1:0], i_v };

	always @(posedge  i_clk)
	if (i_ce)
		f_d <= { f_d[15:0], i_d };

	always @(posedge i_clk)
	if (f_bytecount <= 7'h7f)
		assert(f_bytecount == { 9'h0, r_cnt[6:0] });
	else
		assert(&r_cnt);

	always @(posedge i_clk)
	if ((f_past_valid)&&(i_v)&&(f_bytecount == 17))
		assert(r_hlen == { f_d[19:16], 1'b0 } + 5'h7);
	
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assert(!r_ip);
	else if ((f_v[0])&&(f_bytecount == 15))
	begin
		// Bytes 11 and 12 must be 0x0800 in order for this to be an
		// IP (internet protocol) packet
		// f_bytecount is delayed by one, and then we look into the
		// past for this
		if ((f_d[23:16]==8'h08)&&(f_d[15:8]==8'h00))
			assert(r_ip);
		else
			assert(!r_ip);
	end else if ($past(r_ip)&&(f_bytecount == 17))
	begin
		if ((f_d[23:20] == 4'h4)&&(f_d[19:16] >= 4'h5))
			assert(r_ip);
		else
			assert(!r_ip);
	end else if (!f_v[0])
		assert(!r_ip);
	else
		assert($stable(r_ip));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_en)))
		assert(!o_err);

	wire	[15:0]	f_check;
	assign		f_check = r_check[15:0] + { 15'h0, r_check[16] };

	wire	[15:0]	f_check_when;
	assign		f_check_when = ({ 9'h0, r_hlen, 1'b0 } + 16'd3);

	wire	f_check_now;
	assign	f_check_now = (i_en)&&(f_bytecount == f_check_when)
				&&(f_bytecount >= 17);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assert(!o_err);
	else if ((f_v[0])&&($past(r_ip))&&(r_ip)&&($past(i_en))
			&&($past(i_ce)))
	begin
		if ($past(o_err))
			assert(o_err);
		else if ($past(&r_cnt))
			assert($stable(o_err));
		else if (!f_check_now)
			assert(!o_err);
		else if ($past(f_check) != 16'hffff)
			assert( o_err);
	end else if ((f_past_valid)&&(r_cnt < 17))
		assert(!o_err);
	else if ((f_past_valid)&&(r_cnt > 17))
		assert($stable(o_err));

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_ce))&&($past(!i_en || i_reset)))
		assert(!o_err);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(r_v))&&($past(i_ce)))
		assert(!r_v);

	always @(posedge i_clk)
	if (r_idx < 6'h7)
		assert(!r_ip);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	always @(posedge i_clk)
		cover(r_ip);
	always @(posedge i_clk)
		cover(o_err);

	always @(posedge i_clk)
		cover($fell(i_v) && !o_err && r_ip && !$past(i_reset));


	always @(posedge i_clk)
		cover(r_v && r_idx == 6'h6);
	always @(posedge i_clk)
		cover(r_v && r_idx == 6'h7);
	always @(posedge i_clk)
		cover(r_v && r_idx == 6'h7 && r_ip);
	always @(posedge i_clk)
		cover(r_v && r_idx == 6'h6 && r_word == 16'h0800);
	always @(posedge i_clk)
		cover(r_v && r_idx == 6'h7 && r_ip && r_word[15:8] == 8'h45);//!

	reg	f_long_pkt;
	initial	f_long_pkt = 0;
	always @(posedge i_clk)
	if (i_reset || !i_v)
		f_long_pkt <= 0;
	else if (r_idx == 6'h8 && r_ip && !o_err)
		f_long_pkt <= 1'b1;

	always @(posedge i_clk)
		cover(f_long_pkt && o_err);

`endif
endmodule
