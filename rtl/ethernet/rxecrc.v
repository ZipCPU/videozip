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
			end else begin
				o_v <= r_buf[26];
				o_d <= r_buf[25:18];
			end
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

`endif
endmodule
