////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/rxeipchk.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To cull any IP packets (EtherType=0x0800) from the stream
//		whose packet header checksums don't match.  Also, to cull
//	any IP packets from the stream whose destination address is neither
//	broadcast nor our own.
//
// Drop reasons:
//	Packet *MUST* be of EtherType 0x0800 to be considered
//	1. IPv4, but header length < 5
//	2. Packet length is less than the header length
//	3. IP Checksum doesn't match
//	4. OPTIONAL if OPT_IPADDR_CHECK is set, drop any packet addressed to
//		other IP addresses
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
//
`default_nettype	none
// }}}
module rxeipchk #(
		parameter [0:0]		OPT_IPADDR_CHECK  = 1'b0,
		localparam [31:0]	BROADCAST_IP_ADDR = 32'hffff_ffff
	) (
		// {{{
		// (i_clk, i_reset, i_ce, i_en, i_v, i_d, o_err);
		input	wire		i_clk, i_reset, i_ce, i_en,
		input	wire	[31:0]	i_my_ipaddr,
		input	wire		i_v,	// Valid
		input	wire	[7:0]	i_d,	// Data nibble
		output	reg		o_v,
		output	reg	[7:0]	o_d,
		output	reg		o_err
		// }}}
	);

	// Local declarations
	// {{{
	localparam [15:0]	ETHERTYPE_IP = 16'h0800;
	reg		r_v;
	reg	[15:0]	r_word;
	reg	[15:0]	r_cnt, r_pktlen;
	reg	[5:0]	r_idx;
	reg	[15:0]	hi_addr;

	reg		r_ip;
	reg	[3:0]	r_hlen;
	reg	[16:0]	r_check;
	wire	[5:0]	w_hlen;

	reg		broadcast_ip_addr_flag;
	// }}}

	// r_cnt, r_idx, r_v
	// {{{
	initial	r_cnt = 0;
	initial	r_idx = 0;
	initial	r_v   = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_cnt <= 0;
		r_idx <= 0;
		r_v   <= 0;

		o_v   <= 0;
		o_d   <= 0;
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
			r_idx[4:0] <= r_cnt[5:1];
			r_idx[5] <= (r_cnt[15:6] != 0);
			r_word <= { r_word[7:0], i_d };
		end

		o_v <= i_v && ((!r_ip || !i_en)||(r_cnt < r_pktlen));
		o_d <= i_d;
	end
	// }}}

	// o_err, r_check, r_ip, r_hlen
	// {{{
	assign	w_hlen = { r_hlen, 2'b00 };

	initial	o_err   = 0;
	initial	r_check = 0;
	initial	r_ip    = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		o_err   <= 0;
		r_check <= 0;
		r_ip    <= 0;
		r_hlen  <= 0;
		// }}}
	end else if (i_ce)
	begin
		if (!i_v)
		begin
			// {{{
			// No packet in progress -- clear for the next one
			o_err   <= 0;
			r_check <= 0;
			r_ip    <= 0;
			r_hlen  <= 0;

			r_pktlen<= 14 + 20; // Minimum IPv4 packet size
			// }}}
		end else if (r_v)
		begin
			// {{{
			// *** Process 16'b words here ***
			//

			if (r_idx == 6'h6)
				// Is this actually an IP packet?
				// Check the ethertype field
				r_ip <= (r_word == ETHERTYPE_IP);
			else if ((r_ip)&&(r_idx == 6'h7))
				// Is this actually an IP packet?
				// Check the IP protocol version, make sure we
				// are ipv4
				r_ip <= ((r_word[15:12] == 4'h4)
						&&(r_word[11:8] >= 4'h5));

			// Copy the header length (divided by two)
			if (r_idx == 6'h7)
				r_hlen <= r_word[11:8];

			// Copy the total packet length
			if (r_idx == 6'h8)
				r_pktlen <= r_word[15:0] + 14;

			// Causes for errors:
			// {{{

			// 1. It's an error if we aren't an IPv4 packet or
			//   being an IPv4 packet if the header length isn't at
			//   least 5 words
			if (r_idx == 6'h7)
				o_err <= (r_ip)&&(i_en)
					&&((r_word[15:12] != 4'h4)
					||(r_word[11:8] < 4'h5));

			// 2. If the packet length is less than the header
			//   length
			if (r_ip && r_idx == 6'h8 && (r_word[15:0] <= { {(10){1'b0}}, w_hlen }))
				o_err <= 1;

			// 3. It is an error if the IP header checksum doesn't
			//   match
			//
			// First, calculate that checksum once r_ip gets set.
			if (r_ip)
				r_check <= r_check[15:0] + r_word + { 15'h0, r_check[16]};
			if ((r_idx > 6'h8)&&(r_idx == { 1'b0, r_hlen, 1'b0 } + 5'h7))
				o_err <= (o_err) || ((r_ip)&&(i_en)&&
					((r_check[15:1] != 15'h7fff)
					||((r_check[0]^r_check[16])!=1'b1)));

			// 4. It is an error (i.e. drop this packet) if the
			//   destination IP address is neither a broadcast
			//   address nor our address

			if (r_idx == 6'd15) // Grab the top half of our IP addr
				hi_addr <= r_word;

			if (OPT_IPADDR_CHECK && i_en && r_ip && r_idx == 6'd16
					&& !broadcast_ip_addr_flag
					&& { hi_addr, r_word } != i_my_ipaddr)
				o_err <= 1'b1;
			// }}}
			// }}}
		end
	end

	always @(*)
	begin
		casez(hi_addr[15:13])
		3'b0??: broadcast_ip_addr_flag = ({ hi_addr[7:0], r_word } == 24'hff_ff_ff);
		3'b10?: broadcast_ip_addr_flag = (r_word == 16'hff_ff);
		3'b110: broadcast_ip_addr_flag = (r_word[7:0] == 8'hff);
		3'b111: broadcast_ip_addr_flag = ({ hi_addr, r_word } == BROADCAST_IP_ADDR);
		endcase
	end

	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg		f_past_valid;
	reg	[15:0]	f_bytecount;
	reg	[23:0]	f_d;
	reg	[2:0]	f_v;
	wire	[15:0]	f_check;
	wire	[15:0]	f_check_when;
	wire	f_check_now;
	wire	[15:0]	f_addr_check;
	(* anyconst *) wire [31:0]	f_my_ip_addr;
	(* anyconst *) wire [31:0]	f_pkt_ipaddr;
	wire	f_not_my_packet;
	reg	f_pkt_broadcast_addr;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
		assume(f_my_ip_addr == i_my_ipaddr);

	always @(*)
	begin
		// f_pkt_broadcast_addr = 1'b0;
		casez(f_pkt_ipaddr[31:29])
		3'b0??: f_pkt_broadcast_addr=(f_pkt_ipaddr[23:0] == 24'hffffff);
		3'b10?: f_pkt_broadcast_addr=(f_pkt_ipaddr[15:0] == 16'hffff);
		3'b110: f_pkt_broadcast_addr=(f_pkt_ipaddr[ 7:0] == 8'hff);
		3'b111: f_pkt_broadcast_addr=(f_pkt_ipaddr == 32'hffff_ffff);
		endcase
	end

	// Assume the IP address that arrives matches f_pkt_ipaddr above
	// {{{
	always @(*)
	if (i_v && f_bytecount < 34)
	case(f_bytecount[5:0])
	6'd30: assume(i_d == f_pkt_ipaddr[31:24]); // (6+6+2)+12 + 4(src)
	6'd31: assume(i_d == f_pkt_ipaddr[23:16]);
	6'd32: assume(i_d == f_pkt_ipaddr[15: 8]);
	6'd33: assume(i_d == f_pkt_ipaddr[ 7: 0]);
	default: begin end
	endcase
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We always start with a reset
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	// There's never more than one idle between valid characters
	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	// Valid goes low on reset
	initial	assume(!i_v);
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
		assume(!i_v);

	// Enable stays constant during a burst
	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v)||($past(i_v))))
		assume($stable(i_en));

	// Let's ... just count bytes
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

	// Maximum packet length -- 32760 bytes
	//	This is rather arbitrary here, but it helps our proof
	always @(posedge i_clk)
	if (f_bytecount > 16'd32760)
		assume(!i_v);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Safety properties / assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Shift register representing "valid" data
	initial	f_v = 0;
	always @(posedge  i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[1:0], i_v };

	// 24'bit incoming data shift register
	always @(posedge  i_clk)
	if (i_ce)
		f_d <= { f_d[15:0], i_d };

	// The byte count must match r_cnt for the first 127 bytes
	always @(posedge i_clk)
	if (r_cnt != 16'hffff)
		assert(f_bytecount == r_cnt);

	// Header length ?
	always @(posedge i_clk)
	if ((f_past_valid)&&(i_v)&&(f_bytecount == 17))
		assert(r_hlen == { f_d[19:16], 1'b0 });

	// r_ip ... is this a valid IP packet?
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!r_ip);
	end else if ((f_v[0])&&(f_bytecount == 15))
	begin // Ethertype check
		// {{{
		// Bytes 11 and 12 must be 0x0800 in order for this to be an
		// IP (internet protocol) packet
		// f_bytecount is delayed by one, and then we look into the
		// past for this
		if ((f_d[23:16]==8'h08)&&(f_d[15:8]==8'h00))
		begin
			assert(r_ip);
		end else
			assert(!r_ip);
		// }}}
	end else if ($past(r_ip)&&(f_bytecount == 17))
	begin
		// Must be IP version 4, and header must be 5*4 bytes or longer
		// {{{
		if ((f_d[23:20] == 4'h4)&&(f_d[19:16] >= 4'h5))
		begin
			assert(r_ip);
		end else
			assert(!r_ip);
		// }}}
	end else if (!f_v[0])
	begin
		assert(!r_ip);
	end else
		assert($stable(r_ip));

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_en)))
		assert(!o_err);

	assign	f_not_my_packet = r_ip && (f_my_ip_addr != f_pkt_ipaddr)
			&& !f_pkt_broadcast_addr;

	assign		f_check = r_check[15:0] + { 15'h0, r_check[16] };

	assign		f_check_when = ({ 9'h0, r_hlen, 1'b0 } + 16'd10);

	assign	f_check_now = (i_en)&&(f_bytecount == f_check_when)
				&&(f_bytecount >= 17);
	assign	f_addr_check = (i_en)&&(f_bytecount == 17);
	// o_err
	// {{{
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_err);
	end else if ((f_v[0])&&($past(r_ip))&&(r_ip)&&($past(i_en))
			&&($past(i_ce)))
	begin
		if ($past(o_err))
		begin
			assert(o_err);
		end else if ($past(&r_cnt))
		begin
			assert($stable(o_err));
		end else if (f_not_my_packet && r_idx >= 17)
		begin
			assert(o_err);
		end else if (!f_check_now)
		begin
			assert(!o_err);
		end else if ($past(f_check) != 16'hffff)
			assert( o_err);
	end else if ((f_past_valid)&&(r_cnt < 17))
	begin
		assert(!o_err);
	end else if ((f_past_valid)&&(r_cnt > 17))
		assert($stable(o_err));
	// }}}

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_ce))&&($past(!i_en || i_reset)))
		assert(!o_err);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(r_v))&&($past(i_ce)))
		assert(!r_v);

	always @(posedge i_clk)
	if (r_idx < 6'h7)
		assert(!r_ip);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	f_long_pkt;

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

	initial	f_long_pkt = 0;
	always @(posedge i_clk)
	if (i_reset || !i_v)
		f_long_pkt <= 0;
	else if (r_idx == 6'h8 && r_ip && !o_err)
		f_long_pkt <= 1'b1;

	always @(posedge i_clk)
		cover(f_long_pkt && o_err);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, f_v[2] };
	// Verilator lint_on  UNUSED
	// }}}
`endif
// }}}
endmodule
