////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	txespeed.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	The RGMII ethernet core runs at 125MHz, no less.  It can
//		handle 1Gbps ethernet natively.  However, in order to handle
//	100Mbps or 10Mbps ethernet, it needs to be slowed down.  That's
//	the purpose of this module.
//
//	The desired slowdown is created by create a CE signal that will be
//	true either on every clock cycle (for GbE), or on every 10th clock
//	cycle (for 100MbE), or on every 100th clock cycle for 10MbE.
//
//	A second modification has to deal with the 8-bit outputs.  For
//	GbE, these are straight pass through.  For slower speeds, the output
//	must be done in nibbles, and the two nibbles of the 8-bit output need
//	to be identical.  Here we handle those nibble adjustments as well.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
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
module	txespeed(i_clk, i_reset, i_spd, i_v, i_d, o_v, o_d, o_ce, o_ck);
	parameter		CK10M  = 50;
	parameter		CK100M =  5;
	parameter		CK1G   =   1;
	localparam	[1:0]	SPD10M = 2'b10,
				SPD100M= 2'b01,
				SPD1G  = 2'b00;
	input	wire		i_clk, i_reset;
	input	wire	[1:0]	i_spd;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	reg		o_v;
	output	reg	[7:0]	o_d;
	output	reg		o_ce;
	output	reg	[1:0]	o_ck;

	reg		r_ce, second_half;
	reg	[1:0]	r_spd;
	reg	[6:0]	ck_counter;
	reg	[3:0]	r_buf;

	initial	r_spd = SPD1G;
	always @(posedge i_clk)
	if (i_reset)
		r_spd <= SPD1G;
	else if (!o_v && ((r_spd == SPD1G) || (ck_counter == 1)))
		r_spd <= i_spd;

	initial	ck_counter = 0;
	initial	r_ce = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_ce <= 1;
		ck_counter <= 0;
	end else if (r_ce)
	begin
		case(r_spd)
		SPD10M: begin
			r_ce <= 0;
			ck_counter <= CK10M-1;
			end
		SPD100M: begin
			r_ce <= 0;
			ck_counter <= CK100M-1;
			end
		default: begin
			// SPD1G:
			r_ce <= (CK1G <= 1);
			ck_counter <= CK1G-1;
			end
		endcase

	end else begin
		r_ce       <= (ck_counter <= 1);
		ck_counter <= (ck_counter - 1);
	end

	localparam [6:0] HLF10M  = { 1'b0, CK10M[6:1]  };
	localparam [6:0] HLF100M = { 1'b0, CK100M[6:1] };

	initial	o_ck = 2'b10;
	always @(posedge i_clk)
	if (i_reset)
		o_ck <= 2'b10;
	else if (r_spd == SPD1G)
		o_ck <= 2'b10;
	else if (r_ce)
		o_ck <= 2'b11;
	else if (r_spd == SPD10M)
	begin
		if (CK10M[0] && (ck_counter == HLF10M+1))
			o_ck <= 2'b10;
		else if (ck_counter <= HLF10M)
			o_ck <= 2'b00;
		else
			o_ck <= 2'b11;
	end else // if (r_spd == SPD100M)
	begin
		if (CK100M[0] && (ck_counter == HLF100M+1))
			o_ck <= 2'b10;
		else if (ck_counter <= HLF100M)
			o_ck <= 2'b00;
		else
			o_ck <= 2'b11;
	end

	always @(posedge i_clk)
	if (r_ce)
		r_buf <= i_d[7:4];

	initial	second_half = 1;
	always @(posedge i_clk)
	if (i_reset || r_spd == SPD1G)
		second_half <= 1;
	else if (r_ce)
		second_half <= !second_half;

	initial	o_v = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_v <= 0;
	else if (r_ce && (r_spd == SPD1G || !second_half))
		o_v <= i_v;

	initial	o_d = 0;
	always @(posedge i_clk)
	if (r_ce)
	begin

		if (r_spd == SPD1G)
			o_d <= i_d;
		else if (second_half)
			o_d <= { r_buf[3:0], r_buf[3:0] };
		else
			o_d <= { i_d[3:0], i_d[3:0] };

		if (!i_v && (!o_v || second_half))
		begin
			{ o_d[4], o_d[0] } <= 2'b11;
			case(r_spd)
			SPD100M: { o_d[6:5], o_d[2:1] } <= {(2){ 2'b01 }};
			 SPD10M: { o_d[6:5], o_d[2:1] } <= {(2){ 2'b00 }};
			default: { o_d[6:5], o_d[2:1] } <= {(2){ 2'b10 }};
			endcase
			{ o_d[7], o_d[3] } <= 1;
		end
	end

	initial	o_ce = 0;
	always @(posedge i_clk)
		o_ce <= i_reset || (r_ce && second_half);

`ifdef	FORMAL
	reg	f_past_valid, f_halfway;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our input
	//
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_v);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && $past(i_v && !o_ce))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end

	always @(posedge i_clk)
	if (i_spd != r_spd)
		assume($stable(i_spd));

	always @(*)
		assume(i_spd != 2'b11);

	always @(*)
	if (!i_reset && r_spd != i_spd)
		assume(!i_v);

	always @(posedge i_clk)
	if (f_past_valid && $past(o_v && !i_v))
		assume(!i_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	//
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	if (r_spd == SPD1G)
		assert(ck_counter == 0);
	else if (r_spd == SPD100M)
		assert(ck_counter < CK100M);
	else if (r_spd == SPD10M)
		assert(ck_counter < CK10M);
	else
		assert(r_spd != 2'b11);

	always @(*)
		assert(r_ce == (ck_counter == 0));

	////////////////////////////////////////////////////////////////////////
	//
	// Assertions
	//

	//
	// Speed control
	//
	always @(*)
		assert(r_spd != 2'b11);

	always @(*)
	begin
		f_halfway = 1;
		if (r_spd == SPD10M)
			f_halfway = CK10M[0] && (ck_counter == HLF10M);
		else if (r_spd == SPD100M)
			f_halfway = CK100M[0] && (ck_counter == HLF100M);
	end

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && o_v && $stable(r_spd))
	begin
		if (f_halfway)
			assert(o_ck == 2'b10);
		else if (r_spd == SPD10M)
		begin
			assert(ck_counter < CK10M);
			if (ck_counter >= HLF10M)
				assert(o_ck == 2'b11);
			else
				assert(o_ck == 2'b00);
		end else if (r_spd == SPD100M)
		begin
			assert(ck_counter < CK100M);
			if (ck_counter >= HLF100M)
				assert(o_ck == 2'b11);
			else
				assert(o_ck == 2'b00);
		end else if (r_spd == SPD1G)
		begin
			assert(o_ck == 2'b10);
			assert(ck_counter < CK1G);
			assert(f_halfway);
		end
	end

	always @(*)
		assert(o_ck != 2'b01);
	always @(posedge i_clk)
	if (f_past_valid && $past(r_spd == SPD1G) && (r_spd == SPD1G))
		assert(o_ck == 2'b10);
	else if (f_past_valid && r_spd != SPD1G && $past(r_spd != SPD1G))
		assert(o_ck != 2'b10 || $changed(o_ck));



	//
	// Nothing changes, save on the positive edge of a clock
	//
	always @(posedge i_clk)
	if (f_past_valid && !$rose(o_ck[1]) && r_spd != SPD1G && $past(r_spd != SPD1G))
	begin
		assert($stable(o_v));
		assert(!o_v || $stable(o_d));
	end


	//
	// r_ce
	always @(posedge i_clk)
	if (f_past_valid && !$past(r_ce))
		assert($stable(o_d));

	always @(posedge i_clk)
	if (f_past_valid && $past(i_reset))
		assert(!o_v);

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	reg	[7:0]	cvr_count;
	reg		cvr_check;
	reg	[1:0]	cvr_bits;
	reg		cvr_interesting;

	initial	cvr_count = 8'he0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_count <= 8'he0;
	else if (i_v && o_ce)
		cvr_count <= cvr_count + 1;

	initial	cvr_check = 1;
	always @(posedge i_clk)
	if (i_reset)
		cvr_check <= 1;
	else if (i_v && o_ce && i_d != cvr_count)
		cvr_check <= 0;

	initial	cvr_bits = 0;
	always @(posedge i_clk)
	if (i_reset || (r_spd != i_spd))
		cvr_bits <= 0;
	else if (o_ce && o_v && (!(&cvr_bits)))
		cvr_bits <= cvr_bits + 1;

	always @(*)
		cvr_interesting = f_past_valid && cvr_check && (&cvr_bits);


	/////////////////

	always @(posedge i_clk)
	if (f_past_valid)
		cover($fell(o_v) && !$past(i_reset) && (r_spd == SPD100M)
			&& cvr_interesting);		// !

	always @(posedge i_clk)
	if (f_past_valid)
		cover($fell(o_v) && !$past(i_reset) && (r_spd == SPD1G)
			&& cvr_interesting);		// !

`endif
endmodule
