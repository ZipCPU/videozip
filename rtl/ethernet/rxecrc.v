////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rxecrc.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To detect any CRC errors in the packet as received.  The CRC
//		is not stripped as part of this process.  However, any bytes
//	following the CRC, up to four, will be stripped from the output.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
module	rxecrc(i_clk, i_reset, i_ce, i_en, i_v, i_d, o_v, o_d, o_err);
	localparam [31:0]	TAPS = 32'hedb88320;
	localparam	[0:0]	INVERT = 1'b1;
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;
	output	wire		o_err;

	reg		r_err;
	reg	[2:0]	r_mq; // Partial CRC matches
	reg	[3:0]	r_mp; // Prior CRC matches

	reg	[31:0]	r_crc;
	reg	[23:0]	r_crc_q0;
	reg	[15:0]	r_crc_q1;
	reg	[ 7:0]	r_crc_q2;

	reg	[26:0]	r_buf;

	reg	[31:0]	crc_eqn	[0:7];
	reg	[31:0]	crcvec	[0:255];
	reg	[7:0]	roct;

	integer	k, oct, vecacc;
	initial begin
		crc_eqn[7] = TAPS;
		for(k=6; k>=0; k=k-1)
		begin : INITIAL_CRC_EQN
			if (crc_eqn[k+1][0])
				crc_eqn[k] = { 1'b0, crc_eqn[k+1][31:1] }^ TAPS;
			else
				crc_eqn[k] = { 1'b0, crc_eqn[k+1][31:1] };
		end
	end

	always @(*)
	begin
		for(oct=0; oct<256; oct=oct+1)
		begin : BUILD_CRC_VEC
			roct = oct[7:0];
			vecacc = 0;
			for(k=0; k<8; k=k+1)
			begin : FOREACH_BIT
				if (roct[k])
					vecacc = vecacc ^ crc_eqn[k];
			end
			crcvec[oct] = vecacc;
		end
	end



	wire	[7:0]	lowoctet;
	assign	lowoctet  = r_crc[7:0] ^ i_d;

	wire	[31:0]	shifted_crc;
	assign	shifted_crc = { 8'h0, r_crc[31:8] };

	initial	r_crc = (INVERT==0)? 32'h00 : 32'hffffffff;
	always @(posedge i_clk)
	if (i_reset)
		r_crc <= (INVERT==0)? 32'h00 : 32'hffffffff;
	else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
			r_crc <= (INVERT==0)? 32'h00 : 32'hffffffff;
		else if (i_v)
			/// Calculate the CRC
			r_crc <= shifted_crc ^ crcvec[lowoctet];
	end


	initial	o_v = 0;
	initial	o_d = 8'h0;
	initial	r_buf = 0;
	always @(posedge i_clk)
	begin
		if (i_ce)
		begin
			r_buf <= { r_buf[17:0], i_v, i_d };
			if ((!i_v)&&(r_buf[8]))
			begin
				if (r_mp[3])
				begin
					r_buf[ 8] <= 1'b0;
					r_buf[17] <= 1'b0;
					r_buf[26] <= 1'b0;
				end else if (r_mp[2])
				begin
					r_buf[ 8] <= 1'b0;
					r_buf[17] <= 1'b0;
				end else if (r_mp[1])
					r_buf[8] <= 1'b0;
				// else if (r_mp[0]) ... keep everything
			end

			o_v <= r_buf[26];
			o_d <= r_buf[25:18];
		end

		if (i_reset)
		begin
			r_buf[ 8] <= 1'b0;
			r_buf[17] <= 1'b0;
			r_buf[26] <= 1'b0;

			o_v <= 0;
			o_d <= 8'h0;
		end
	end
		
	initial r_err = 1'b0;
	initial	r_mq  = 0;
	initial	r_mp  = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_crc_q0 <= 0;
		r_crc_q1 <= 0;
		r_crc_q2 <= 0;

		r_err <= 1'b0;
		r_mq[2:0] <= 3'h0;
		r_mp <= 4'h0;
	end else if (i_ce)
	begin
		r_crc_q0 <= r_crc[31:8];
		r_crc_q1 <= r_crc_q0[23:8];
		r_crc_q2 <= r_crc_q1[15:8];

		if ((!i_v)&&(!o_v))
		begin
			r_err <= 1'b0;
			r_mq[2:0] <= 3'h0;
			r_mp <= 4'h0;
		end else
		begin
			if (i_v)
			begin
				r_mq[0] <=            (i_d == ((INVERT)?~r_crc[   7:0]:r_crc[7:0]));
				r_mq[1] <= (r_mq[0])&&(i_d == ((INVERT)?~r_crc_q0[7:0]:r_crc_q0[7:0]));
				r_mq[2] <= (r_mq[1])&&(i_d == ((INVERT)?~r_crc_q1[7:0]:r_crc_q1[7:0]));
			end else
				r_mq <= 0;

			r_mp <= { r_mp[2:0], 
				(r_mq[2])&&(i_v)&&(i_d == (~r_crc_q2[7:0])) };

			// Now, we have an error if ...
			// On the first empty, none of the prior N matches
			// matched.
			r_err <= (r_err)||((i_en)&&(!i_v)&&(r_buf[8])&&(r_mp == 4'h0));
		end
	end

	assign o_err = r_err;


////////////////////////////////////////////////////////////////////////////////
//
//
//
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	reg	[4:0]	f_v;
	reg		f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	initial	f_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		f_v <= 0;
	else if (i_ce)
		f_v <= { f_v[3:0], i_v };

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	//
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (i_reset)
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v) || (o_v)))
		assume(i_en == $past(i_en));


	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_v))&&(o_v))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&((o_v)||(i_v)))
		assume(i_en == $past(i_en));

	// i_v cannot restart while o_v is active
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))
			&&($past(o_v))
			&&(!$past(i_v)))
		assume(!i_v);

	always @(posedge i_clk)
	if (f_v != 0)
	begin
		if (!f_v[4])
			assume(i_v);
		else if (!f_v[0])
			assume(!i_v);
	end
			
	//always @(posedge i_clk)
	//if ((f_past_valid)&&($past(o_v))&&(!$past(i_v))&&(!$past(i_reset)))

	/*
	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_v))&&(!$past(i_reset)))
	begin
		assert(o_v);
		assert(o_d == $past(i_d));
	end
	*/
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		// Test initial/reset conditions
		assert(r_crc == (INVERT==0)? 32'h00 : 32'hffffffff);
		assert(o_v   == 1'b0);
		assert(o_d   == 8'h0);
	end

	always @(*)
	begin
		assert(!r_buf[ 8] || f_v[0] == r_buf[ 8]);
		assert(!r_buf[17] || f_v[1] == r_buf[17]);
		assert(!r_buf[26] || f_v[2] == r_buf[26]);

		if (f_v != 0)
			assert((f_v == 5'h01)||(f_v == 5'h03)
				||(f_v == 5'h07)||(f_v == 5'h0f)
				||(f_v == 5'h1f)||(f_v == 5'h1e)
				||(f_v == 5'h1c)||(f_v == 5'h18)
				||(f_v == 5'h10));
	end



	reg	[31:0]	f_pre_crc	[7:0];
	reg	[31:0]	f_crc;

	// Need to verify the CRC
	always @(*)
	begin : GEN_PRECRC
		if (i_d[0] ^ r_crc[0])
			f_pre_crc[0] = { 1'b0, r_crc[31:1] } ^ TAPS;
		else
			f_pre_crc[0] = { 1'b0, r_crc[31:1] };

		for(k=1; k<8; k=k+1)
		begin
			if (f_pre_crc[k-1][0]^i_d[k])
				f_pre_crc[k] = { 1'b0, f_pre_crc[k-1][31:1] } ^ TAPS;
			else
				f_pre_crc[k] = { 1'b0, f_pre_crc[k-1][31:1] };
		end

		f_crc = f_pre_crc[7];
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_v && i_ce)))
		assert(r_crc == $past(f_crc));

	////////////////////////////////////////////////////////////////////////
	//
	// Cover Properties
	//
	always @(posedge i_clk)
	if ($past(!i_reset && i_en))
	begin
		cover(f_past_valid && $fell(o_v) && $past(o_err));
		cover(f_past_valid && $fell(o_v) && o_err);
		cover(f_past_valid && $fell(o_v) && $past(!o_err));
		cover(f_past_valid && $fell(o_v) && !o_err);
	end

	////////////////////////////////////////////////////////////////////////	//
	// Known packet properties
	//
	// The following properties test two known packets, which are known to
	// have the right CRCs.  (Or ... at least I suspect so, they were
	// received on my local LAN)  Let's make some assertions that this
	// CRC receiver will
	reg	[69:0]	v1;
	reg	[4:0]	v1e;

	initial	v1 = 0;
	initial	v1e = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		v1 <= 0;
		v1e <= 0;
	end else if (i_ce) begin
		v1 <= { v1[68:0], (!i_v) };
		if ((!i_v)||(i_d != 8'hff))
			v1[1] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[2] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[3] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[4] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[5] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[6] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc8))
			v1[7] <= 1'b0;
		if ((!i_v)||(i_d != 8'h3a))
			v1[8] <= 1'b0;
		if ((!i_v)||(i_d != 8'h35))
			v1[9] <= 1'b0;
		if ((!i_v)||(i_d != 8'hd2))
			v1[10] <= 1'b0;
		if ((!i_v)||(i_d != 8'h07))
			v1[11] <= 1'b0;
		if ((!i_v)||(i_d != 8'hb1))
			v1[12] <= 1'b0;
		if ((!i_v)||(i_d != 8'h08))
			v1[13] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v1[14] <= 1'b0;
		if ((!i_v)||(i_d != 8'h45))
			v1[15] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v1[16] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v1[17] <= 1'b0;
		if ((!i_v)||(i_d != 8'h24))
			v1[18] <= 1'b0;
		if ((!i_v)||(i_d != 8'h33))
			v1[19] <= 1'b0;
		if ((!i_v)||(i_d != 8'h76))
			v1[20] <= 1'b0;
		if ((!i_v)||(i_d != 8'h40))
			v1[21] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v1[22] <= 1'b0;
		if ((!i_v)||(i_d != 8'h40))
			v1[23] <= 1'b0;
		if ((!i_v)||(i_d != 8'h11))
			v1[24] <= 1'b0;
		if ((!i_v)||(i_d != 8'h67))
			v1[25] <= 1'b0;
		if ((!i_v)||(i_d != 8'h02))
			v1[26] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc0))
			v1[27] <= 1'b0;
		if ((!i_v)||(i_d != 8'ha8))
			v1[28] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0f))
			v1[29] <= 1'b0;
		if ((!i_v)||(i_d != 8'h01))
			v1[30] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc0))
			v1[31] <= 1'b0;
		if ((!i_v)||(i_d != 8'ha8))
			v1[32] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0f))
			v1[33] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v1[34] <= 1'b0;
		if ((!i_v)||(i_d != 8'h05))
			v1[35] <= 1'b0;
		if ((!i_v)||(i_d != 8'hfe))
			v1[36] <= 1'b0;
		if ((!i_v)||(i_d != 8'h05))
			v1[37] <= 1'b0;
		if ((!i_v)||(i_d != 8'hfe))
			v1[38] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v1[39] <= 1'b0;
		if ((!i_v)||(i_d != 8'h10))
			v1[40] <= 1'b0;
		if ((!i_v)||(i_d != 8'hb5))
			v1[41] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0b))
			v1[42] <= 1'b0;
		if ((!i_v)||(i_d != 8'h54))
			v1[43] <= 1'b0;
		if ((!i_v)||(i_d != 8'h43))
			v1[44] <= 1'b0;
		if ((!i_v)||(i_d != 8'h46))
			v1[45] <= 1'b0;
		if ((!i_v)||(i_d != 8'h32))
			v1[46] <= 1'b0;
		if ((!i_v)||(i_d != 8'h04))
			v1[47] <= 1'b0;
		//
		if ((!i_v)||(i_d != 8'h00))
			v1[60:48] <= 1'b0;
		//
		if ((!i_v)||(i_d != 8'h76))
			v1[61] <= 1'b0;
		if ((!i_v)||(i_d != 8'h49))
			v1[62] <= 1'b0;
		if ((!i_v)||(i_d != 8'h97))
			v1[63] <= 1'b0;
		if ((!i_v)||(i_d != 8'hda))
			v1[64] <= 1'b0;
		if (i_v)
			v1[65] <= 1'b0;

		v1e[4:0] <= { v1e[3:0], 1'b0 };
		if ((v1[61])&&(i_v)&&(i_d != 8'h76))
			v1e[0] <= 1'b1;
		if ((v1[62])&&(i_v)&&(i_d != 8'h49))
			v1e[1] <= 1'b1;
		if ((v1[63])&&(i_v)&&(i_d != 8'h97))
			v1e[2] <= 1'b1;
		if ((v1[64])&&(i_v)&&(i_d != 8'hda))
			v1e[3] <= 1'b1;
		if (i_v)
			v1e[4] <= 1'b0;
		if (v1e[4])
			assert(o_err);

		if (v1[64])
			assert(o_v && o_d == 8'h76);
		if (v1[65])
			assert(o_v && o_d == 8'h49);
		if (v1[66])
			assert(o_v && o_d == 8'h97);
		if (v1[67])
			assert(o_v && o_d == 8'hda);
		if (v1[68])
			assert(!o_v);

		if (|v1[69:1])
			assert(!o_err);
		if (v1[ 1]) assert(v1[69: 2] == 0);
		if (v1[ 2]) assert(v1[69: 3] == 0);
		if (v1[ 3]) assert(v1[69: 4] == 0);
		if (v1[ 4]) assert(v1[69: 5] == 0);
		if (v1[ 5]) assert(v1[69: 6] == 0);
		if (v1[ 6]) assert(v1[69: 7] == 0);
		if (v1[ 7]) assert(v1[69: 8] == 0);
		if (v1[ 8]) assert(v1[69: 9] == 0);
		if (v1[ 9]) assert(v1[69:10] == 0);
		if (v1[10]) assert(v1[69:11] == 0);
		if (v1[11]) assert(v1[69:12] == 0);
		if (v1[12]) assert(v1[69:13] == 0);
		if (v1[13]) assert(v1[69:14] == 0);
		if (v1[14]) assert(v1[69:15] == 0);
		if (v1[15]) assert(v1[69:16] == 0);
		if (v1[16]) assert(v1[69:17] == 0);
		if (v1[17]) assert(v1[69:18] == 0);
		if (v1[18]) assert(v1[69:19] == 0);
		if (v1[19]) assert(v1[69:20] == 0);
		if (v1[20]) assert(v1[69:21] == 0);
		if (v1[21]) assert(v1[69:22] == 0);
		if (v1[22]) assert(v1[69:23] == 0);
		if (v1[23]) assert(v1[69:24] == 0);
		if (v1[24]) assert(v1[69:25] == 0);
		if (v1[25]) assert(v1[69:26] == 0);
		if (v1[26]) assert(v1[69:27] == 0);
		if (v1[27]) assert(v1[69:28] == 0);
		if (v1[28]) assert(v1[69:29] == 0);
		if (v1[29]) assert(v1[69:30] == 0);
		if (v1[30]) assert(v1[69:31] == 0);
		if (v1[31]) assert(v1[69:32] == 0);
		if (v1[32]) assert(v1[69:33] == 0);
		if (v1[33]) assert(v1[69:34] == 0);
		if (v1[34]) assert(v1[69:35] == 0);
		if (v1[35]) assert(v1[69:36] == 0);
		if (v1[36]) assert(v1[69:37] == 0);
		if (v1[37]) assert(v1[69:38] == 0);
		if (v1[38]) assert(v1[69:39] == 0);
		if (v1[39]) assert(v1[69:40] == 0);
		if (v1[40]) assert(v1[69:41] == 0);
		if (v1[41]) assert(v1[69:42] == 0);
		if (v1[42]) assert(v1[69:43] == 0);
		if (v1[43]) assert(v1[69:44] == 0);
		if (v1[44]) assert(v1[69:45] == 0);
		if (v1[45]) assert(v1[69:46] == 0);
		if (v1[46]) assert(v1[69:47] == 0);
		if (v1[47]) assert(v1[69:48] == 0);
		if (v1[48]) assert(v1[69:49] == 0);
		if (v1[49]) assert(v1[69:50] == 0);
	end

	//
	//
	//
	reg	[69:0]	v2;
	reg	[4:0]	v2e;

	initial	v2 = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		v2  <= 0;
		v2e <= 0;
	end else if (i_ce) begin
		v2 <= { v2[68:0], (!i_v) };
		if ((!i_v)||(i_d != 8'hff))
			v2[1] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[2] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[3] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[4] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[5] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[6] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc8))
			v2[7] <= 1'b0;
		if ((!i_v)||(i_d != 8'h3a))
			v2[8] <= 1'b0;
		if ((!i_v)||(i_d != 8'h35))
			v2[9] <= 1'b0;
		if ((!i_v)||(i_d != 8'hd2))
			v2[10] <= 1'b0;
		if ((!i_v)||(i_d != 8'h07))
			v2[11] <= 1'b0;
		if ((!i_v)||(i_d != 8'hb1))
			v2[12] <= 1'b0;
		if ((!i_v)||(i_d != 8'h08))
			v2[13] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v2[14] <= 1'b0;
		if ((!i_v)||(i_d != 8'h45))
			v2[15] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v2[16] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v2[17] <= 1'b0;
		if ((!i_v)||(i_d != 8'h24))
			v2[18] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0b))
			v2[19] <= 1'b0;
		if ((!i_v)||(i_d != 8'hca))
			v2[20] <= 1'b0;
		if ((!i_v)||(i_d != 8'h40))
			v2[21] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v2[22] <= 1'b0;
		if ((!i_v)||(i_d != 8'h40))
			v2[23] <= 1'b0;
		if ((!i_v)||(i_d != 8'h11))
			v2[24] <= 1'b0;
if (v2[24])
	assert(o_v && o_d == 8'h40);
		if ((!i_v)||(i_d != 8'h8e))
			v2[25] <= 1'b0;
		if ((!i_v)||(i_d != 8'hae))
			v2[26] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc0))
			v2[27] <= 1'b0;
		if ((!i_v)||(i_d != 8'ha8))
			v2[28] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0f))
			v2[29] <= 1'b0;
		if ((!i_v)||(i_d != 8'h01))
			v2[30] <= 1'b0;
		if ((!i_v)||(i_d != 8'hc0))
			v2[31] <= 1'b0;
		if ((!i_v)||(i_d != 8'ha8))
			v2[32] <= 1'b0;
		if ((!i_v)||(i_d != 8'h0f))
			v2[33] <= 1'b0;
		if ((!i_v)||(i_d != 8'hff))
			v2[34] <= 1'b0;
if (v2[34])
	assert(o_v && o_d == 8'hc0);

		if ((!i_v)||(i_d != 8'h82))
			v2[35] <= 1'b0;
		if ((!i_v)||(i_d != 8'h66))
			v2[36] <= 1'b0;
		if ((!i_v)||(i_d != 8'h05))
			v2[37] <= 1'b0;
		if ((!i_v)||(i_d != 8'hfe))
			v2[38] <= 1'b0;
		if ((!i_v)||(i_d != 8'h00))
			v2[39] <= 1'b0;
		if ((!i_v)||(i_d != 8'h10))
			v2[40] <= 1'b0;
		if ((!i_v)||(i_d != 8'h38))
			v2[41] <= 1'b0;
		if ((!i_v)||(i_d != 8'ha3))
			v2[42] <= 1'b0;
		if ((!i_v)||(i_d != 8'h54))
			v2[43] <= 1'b0;
		if ((!i_v)||(i_d != 8'h43))
			v2[44] <= 1'b0;
		if ((!i_v)||(i_d != 8'h46))
			v2[45] <= 1'b0;
		if ((!i_v)||(i_d != 8'h32))
			v2[46] <= 1'b0;
		if ((!i_v)||(i_d != 8'h04))
			v2[47] <= 1'b0;
		//
		if ((!i_v)||(i_d != 8'h00))
			v2[60:48] <= 1'b0;
		//
		if ((!i_v)||(i_d != 8'ha7))
			v2[61] <= 1'b0;
		if ((!i_v)||(i_d != 8'h2e))
			v2[62] <= 1'b0;
		if ((!i_v)||(i_d != 8'h5e))
			v2[63] <= 1'b0;
		if ((!i_v)||(i_d != 8'hd4))
			v2[64] <= 1'b0;
		if (i_v)
			v2[65] <= 1'b0;

		if (v2[64])
			assert(o_v && o_d == 8'ha7);
		if (v2[65])
			assert(o_v && o_d == 8'h2e);
		if (v2[66])
			assert(o_v && o_d == 8'h5e);
		if (v2[67])
			assert(o_v && o_d == 8'hd4);
		if (v2[68])
			assert(!o_v);

		v2e[4:0] <= { v2e[3:0], 1'b0 };
		if ((v2[62])&&(i_v)&&(i_d != 8'ha7))
			v2e[0] <= 1'b1;
		if ((v2[63])&&(i_v)&&(i_d != 8'h2e))
			v2e[1] <= 1'b1;
		if ((v2[64])&&(i_v)&&(i_d != 8'h5e))
			v2e[2] <= 1'b1;
		if ((v2[65])&&(i_v)&&(i_d != 8'hd4))
			v2e[3] <= 1'b1;
		if (i_v)
			v2e[4] <= 1'b0;
		if (v2e[4])
			assert(o_err);

		if (|v2[66:1])
			assert(!o_err);
		if (v2[ 1]) assert(v2[69: 2] == 0);
		if (v2[ 2]) assert(v2[69: 3] == 0);
		if (v2[ 3]) assert(v2[69: 4] == 0);
		if (v2[ 4]) assert(v2[69: 5] == 0);
		if (v2[ 5]) assert(v2[69: 6] == 0);
		if (v2[ 6]) assert(v2[69: 7] == 0);
		if (v2[ 7]) assert(v2[69: 8] == 0);
		if (v2[ 8]) assert(v2[69: 9] == 0);
		if (v2[ 9]) assert(v2[69:10] == 0);
		if (v2[10]) assert(v2[69:11] == 0);
		if (v2[11]) assert(v2[69:12] == 0);
		if (v2[12]) assert(v2[69:13] == 0);
		if (v2[13]) assert(v2[69:14] == 0);
		if (v2[14]) assert(v2[69:15] == 0);
		if (v2[15]) assert(v2[69:16] == 0);
		if (v2[16]) assert(v2[69:17] == 0);
		if (v2[17]) assert(v2[69:18] == 0);
		if (v2[18]) assert(v2[69:19] == 0);
		if (v2[19]) assert(v2[69:20] == 0);
		if (v2[20]) assert(v2[69:21] == 0);
		if (v2[21]) assert(v2[69:22] == 0);
		if (v2[22]) assert(v2[69:23] == 0);
		if (v2[23]) assert(v2[69:24] == 0);
		if (v2[24]) assert(v2[69:25] == 0);
		if (v2[25]) assert(v2[69:26] == 0);
		if (v2[26]) assert(v2[69:27] == 0);
		if (v2[27]) assert(v2[69:28] == 0);
		if (v2[28]) assert(v2[69:29] == 0);
		if (v2[29]) assert(v2[69:30] == 0);
		if (v2[30]) assert(v2[69:31] == 0);
		if (v2[31]) assert(v2[69:32] == 0);
		if (v2[32]) assert(v2[69:33] == 0);
		if (v2[33]) assert(v2[69:34] == 0);
		if (v2[34]) assert(v2[69:35] == 0);
		if (v2[35]) assert(v2[69:36] == 0);
		if (v2[36]) assert(v2[69:37] == 0);
		if (v2[37]) assert(v2[69:38] == 0);
		if (v2[38]) assert(v2[69:39] == 0);
		if (v2[39]) assert(v2[69:40] == 0);
		if (v2[40]) assert(v2[69:41] == 0);
		if (v2[41]) assert(v2[69:42] == 0);
		if (v2[42]) assert(v2[69:43] == 0);
		if (v2[43]) assert(v2[69:44] == 0);
		if (v2[44]) assert(v2[69:45] == 0);
		if (v2[45]) assert(v2[69:46] == 0);
		if (v2[46]) assert(v2[69:47] == 0);
		if (v2[47]) assert(v2[69:48] == 0);
		if (v2[48]) assert(v2[69:49] == 0);
		if (v2[49]) assert(v2[69:50] == 0);
	end

	always @(*)
	begin
		assert(v1[18:0] == v2[18:0]);
		if (|v1[64:19])
			assert(v2 == 0);
		if (|v2[64:19])
			assert(v1 == 0);
	end

	always @(*)
		cover(v1[69]);
	always @(*)
		cover(v2[69]);

// Tests
//	The other MAC is ff:ff:ff:ff:ff:ff
// 
	// RX[ 0]: 0xc83a35d2
	// RX[ 1]: 0x07b10800
	// RX[ 2]: 0x45000024
	// RX[ 3]: 0x33764000
	// RX[ 4]: 0x40116702
	// RX[ 5]: 0xc0a80f01
	// RX[ 6]: 0xc0a80fff
	// RX[ 7]: 0x05fe05fe
	// RX[ 8]: 0x0010b50b
	// RX[ 9]: 0x54434632
	// RX[10]: 0x04000000
	// RX[11]: 0x00000000
	// RX[12]: 0x00000000
	// RX[13]: 0x00007649
	// RX[14]: 0x97da0000
// Final Rx Status = 0e08403b
`endif
endmodule
