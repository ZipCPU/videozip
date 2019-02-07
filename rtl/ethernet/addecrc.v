////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	addecrc.v
//
// Project:	Ethernet cores, a set of ethernet cores for RM interfaces
//
// Purpose:	To (optionally) add a CRC to a stream of nibbles.   The CRC
//		is calculated from the stream.
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
module addecrc(i_clk, i_reset, i_ce, i_en, i_v, i_d, o_v, o_d);
	// localparam [31:0]	TAPS = 32'h1db71064;
	localparam [31:0]	TAPS = 32'hedb88320;
	localparam	INVERT = 1; // Proper operation requires INVERT=1
	input	wire		i_clk, i_reset, i_ce, i_en;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;

	reg	[3:0]	r_p;
	reg	[31:0]	r_crc;
	wire	[7:0]	lowoctet;
	wire	[31:0]	shifted_crc;

	assign	lowoctet = r_crc[7:0] ^ i_d;
	assign	shifted_crc = { 8'h0, r_crc[31:8] };

	integer	k, oct;

	reg	[31:0]	crc_eqn	[0:7];
	reg	[31:0]	crcvec	[0:255];
	reg	[7:0]	roct;
	integer	vecacc;
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
		// crcvec[8'h80] = crc_eqn[7];
`ifdef	FORMAL
		assert(crcvec[8'h80] == TAPS);
		assert(crcvec[8'h40] == { 1'b0, TAPS[31:1] });
		assert(crcvec[8'h20] == { 2'b0, TAPS[31:2] });
		assert(crcvec[8'h10] == { 3'b0, TAPS[31:3] });
`endif
	end

	////////////////////
	//
	//
	//
	////////////////////
	//
	//
	initial	o_v = 1'b0;
	initial	r_crc = (INVERT==0)? 32'h00 : 32'hffffffff;
	initial	r_p = 4'hf;
	initial	o_v = 1'b0;
	initial	o_d = 8'h0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_crc <= (INVERT==0)? 32'h00 : 32'hffffffff;
		r_p   <= 4'hf;
		o_v   <= 1'b0;
		o_d   <= 8'h0;
	end else if (i_ce)
	begin
		if ((!i_v)&&(!o_v))
		begin
			// Reset the interface
			r_crc <= (INVERT==0)? 32'h00 : 32'hffffffff;
			r_p <= 4'hf;
			o_v <= 1'b0;
			o_d <= 8'h0;
		end else if (i_v)
		begin
			o_v <= i_v;
			r_p <= 4'hf;
			o_d <= i_d;

			r_crc <= shifted_crc ^ crcvec[lowoctet];
		end else begin // if o_v
			// Flush out the CRC
			r_p <= { r_p[2:0], 1'b0 };
			o_v <= (i_en)?r_p[3]:1'b0;
			o_d <= r_crc[7:0] ^ ((INVERT==0)? 8'h0:8'hff);
			r_crc <= { 8'h0, r_crc[31:8] };
		end
	end

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge  i_clk)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Incoming assumptions
	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (i_reset)
		assume(!i_v);

	always @(posedge i_clk)
	if (!$past(i_ce))
		assume(i_ce);

	always @(posedge i_clk)
	if (!$past(i_ce))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&((i_v) || (o_v)))
		assume($stable(i_en));


	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_v))&&(o_v))
		assume(!i_v);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&((o_v)||(i_v)))
		assume($stable(i_en));

	// i_v cannot restart while o_v is active
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_v))&&(!$past(i_v)))
		assume(!i_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Formal assertions
	//

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		// Test initial/reset conditions
		assert(r_crc == (INVERT==0)? 32'h00 : 32'hffffffff);
		assert(r_p   == 4'hf);
		assert(o_v   == 1'b0);
		assert(o_d   == 8'h0);
	end


	//if ((f_past_valid)&&($past(o_v))&&(!$past(i_v))&&(!$past(i_reset)))

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(i_v))&&(!$past(i_reset))&&($past(i_ce)))
	begin
		assert(o_v);
		assert(o_d == $past(i_d));
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_v))&&(!$past(i_v))
		&&($past(i_ce)))
		assert(r_p == { $past(r_p[2:0]), 1'b0 } );

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_en))&&($past(i_ce))
			&&($past(o_v))&&(!$past(i_v)))
		assert(o_v == $past(r_p[3]));

	reg	[31:0]	pre_crc	[7:0];
	reg	[31:0]	f_crc;

	// Need to verify the CRC
	always @(*)
	begin : GEN_PRECRC
		if (i_d[0] ^ r_crc[0])
			pre_crc[0] = { 1'b0, r_crc[31:1] } ^ TAPS;
		else
			pre_crc[0] = { 1'b0, r_crc[31:1] };

		for(k=1; k<8; k=k+1)
		begin
			if (pre_crc[k-1][0]^i_d[k])
				pre_crc[k] = { 1'b0, pre_crc[k-1][31:1] } ^ TAPS;
			else
				pre_crc[k] = { 1'b0, pre_crc[k-1][31:1] };
		end

		f_crc = pre_crc[7];
	end

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_v))&&($past(i_ce)))
		assert(r_crc == $past(f_crc));
`endif
endmodule

