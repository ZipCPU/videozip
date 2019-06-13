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
module	txespeed(i_clk, i_reset, i_spd, i_v, i_d, o_v, o_d, o_ce, o_ck);
	parameter		CK10M  = 50;
	parameter		CK100M =  5;
	parameter		CK1G   =   1;
	parameter		DEADOCTETS = 6;
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

	reg		r_busy, r_ce, halfway, new_spd, second_half;
	reg	[1:0]	r_spd;
	reg	[6:0]	ck_counter;
	reg	[3:0]	r_buf;
	reg	[3:0]	deadtime;

	initial	r_spd = SPD1G;
	always @(posedge i_clk)
	if (i_reset)
		r_spd <= SPD1G;
	else if (!r_busy)
		r_spd <= i_spd;

	always @(*)
		new_spd = (!r_busy && r_spd != i_spd);

	initial	ck_counter = 0;
	initial	halfway = 0;
	initial	r_ce = 1;
	always @(posedge i_clk)
	if (r_ce)
	begin
		case(r_spd)
		SPD10M: begin
			r_ce <= 0;
			ck_counter <= CK10M-1;
			halfway <= (CK10M<=2);
			end
		SPD100M: begin
			r_ce <= 0;
			ck_counter <= CK100M-1;
			halfway <= (CK100M<=2);
			end
		default: begin
			// SPD1G:
			r_ce <= 1;
			ck_counter <= CK1G-1;
			halfway <= 1;
			end
		endcase

	end else begin
		r_ce       <= (ck_counter <= 1);
		ck_counter <= (ck_counter - 1);
		halfway    <= 0;
		if (r_spd == SPD10M)
			halfway <= (ck_counter == (CK10M/2)+1);
		else if (r_spd == SPD100M)
			halfway <= (ck_counter == (CK100M/2)+1);
	end

	initial	o_ck = 2'b10;
	always @(posedge i_clk)
	if (r_spd == SPD1G)
		o_ck <= 2'b10;
	else if (r_spd == SPD10M)
	begin
		if (ck_counter < (CK10M-CK10M[0])/2)
			o_ck <= 2'b00;
		else if (CK10M[0] && (ck_counter == (CK10M-1)/2))
			o_ck <= 2'b10;
		else
			o_ck <= 2'b11;
	end else // if (r_spd == SPD100M)
	begin
		if (ck_counter < (CK100M-CK100M[0])/2)
			o_ck <= 2'b00;
		else if (CK100M[0] && (ck_counter == (CK100M-1)/2))
			o_ck <= 2'b10;
		else
			o_ck <= 2'b11;
	end

	always @(posedge i_clk)
	if (r_ce)
		r_buf <= i_d[7:4];

	initial	second_half = 0;
	always @(posedge i_clk)
	if (r_spd == SPD1G)
		second_half <= 1;
	else if (r_ce)
		second_half <= !second_half;

	initial	o_v = 0;
	always @(posedge i_clk)
	if (i_reset || new_spd)
		o_v <= 0;
	else if (r_ce)
	begin
		if (o_v)
			o_v <= (i_v || second_half);
		else
			o_v <= i_v && !r_busy;
	end

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
	end


	initial	deadtime = 0;
	initial	r_busy   = 1;
	always @(posedge i_clk)
	if (i_reset)
	begin
		deadtime <= 0;
		r_busy   <= 1;
	end else if (!r_busy && r_spd != i_spd)
	begin
		deadtime <= 0;
		r_busy   <= 1;
	end else if (r_ce)
	begin
		if (i_v)
		begin
			deadtime <= 0;
			r_busy   <= 1;
		end else if (r_busy && !o_v && second_half)
			deadtime <= deadtime + 1;

		if (deadtime >= DEADOCTETS)
		begin
			r_busy   <= 0;
			deadtime <= 0;
		end
	end

	initial	o_ce = 0;
	always @(posedge i_clk)
		o_ce <= r_ce & (o_v || !r_busy) && (second_half);

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// Assumptions about our input
	//
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!i_v);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && !$past(o_ce))
	begin
		assume($stable(i_v));
		assume($stable(i_d));
	end

	always @(posedge i_clk)
	if (f_past_valid && $changed(i_spd))
		assume(!$rose(i_v));

	always @(posedge i_clk)
	if (f_past_valid && ($past(i_v) || $past(r_busy)))
		assume($stable(i_spd));

	always @(*)
		assume(i_spd != 2'b11);

	always @(posedge i_clk)
	if (!$past(o_ce))
		assume(!$fell(i_v));

	////////////////////////////////////////////////////////////////////////
	//
	// Assertions
	//

	//
	// Speed control
	//
	always @(*)
		assert(r_spd != 2'b11);

	always @(posedge i_clk)
	if (f_past_valid && !$past(i_reset) && o_v) // $stable(r_spd))
	begin
		if (r_spd == SPD10M)
		begin
			assert(ck_counter < CK10M);
			assert(halfway == (ck_counter == (CK10M/2)));
			if (halfway || ck_counter > CK10M/2)
				assert(o_ck == 2'b11);
			else if ($past(halfway) && CK100M[0])
				assert(o_ck == 2'b10);
			else
				assert(o_ck == 2'b00);
		end else if (r_spd == SPD100M)
		begin
			assert(ck_counter < CK100M);
			assert(halfway == (ck_counter == (CK100M/2)));
			if (halfway || ck_counter > CK100M/2)
				assert(o_ck == 2'b11);
			else if ($past(halfway) && CK100M[0])
				assert(o_ck == 2'b10);
			else
				assert(o_ck == 2'b00);
		end else if (r_spd == SPD1G)
		begin
			assert(o_ck == 2'b10);
			assert(ck_counter < CK1G);
			assert(halfway);
		end
	end

	//
	// Nothing changes, save on the positive edge of a clock
	//
	always @(posedge i_clk)
	if (f_past_valid && !$rose(o_ck[1]) && r_spd != SPD1G)
	begin
		assert($stable(o_v));
		assert($stable(o_d));
	end


	//
	// Busy / dead time
	//
	always @(*)
	if (o_v)
		assert(r_busy);

	always @(*)
		assert(deadtime <= DEADOCTETS);

	always @(*)
	if (!r_busy)
		assert(deadtime == 0);

	always @(posedge i_clk)
	if ((deadtime > 0)&&(!o_ce))
		assert(!o_v);

	//
	// r_ce
	always @(posedge i_clk)
	if (f_past_valid && !$past(r_ce))
		assert($stable(o_d));

	//
	// Transmit sequence
	(* anyconst *)	reg	[7:0]	f_special_data;
	reg	txseq;

	initial	txseq = 0;
	always @(posedge i_clk)
	if (i_reset)
		txseq <= 0;
	else begin
		txseq <= txseq << 1;

		if (f_past_valid && i_v && (o_v || !r_busy) && $stable(r_spd)
				&& i_d == f_special_data)
			txseq[0] <= 1;

		txseq[1] <= 0;
		if ((r_spd == SPD1G)&&(txseq[0]))
			assert(o_v && o_d == f_special_data);
		else if ((r_spd != SPD1G)&&(txseq[0]))
		begin
			assert(o_v && o_d[7:4] == f_special_data[7:4]);
			txseq[1] <= 1;
		end

		// txseq[2] <= txseq[1];
		if (txseq[1] || txseq[2])
		begin
			if (!r_ce)
				txseq[3] <= 0;
			else
				txseq[3:2] <= 2'b10;

			assert(o_v && o_d == {(2){f_special_data[7:4]}});
		end

		if (txseq[3])
			assert(o_v && o_d == {(2){f_special_data[3:0]}});
	end
		

	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	//
	reg	[7:0]	cvr_count;
	reg		cvr_check;
	reg	[1:0]	cvr_bits;

	initial	cvr_count = 8'h40;
	always @(posedge i_clk)
	if (i_reset)
		cvr_count <= 8'h40;
	else if ((i_v || r_busy) && o_ce)
		cvr_count <= cvr_count + 1;

	initial	cvr_check = 1;
	always @(posedge i_clk)
	if (i_reset)
		cvr_check <= 0;
	else if ((i_v || r_busy) && o_ce && i_d != cvr_count)
		cvr_check <= 0;

	initial	cvr_bits = 0;
	always @(posedge i_clk)
	if (i_reset || new_spd)
		cvr_bits <= 0;
	else if (o_ce && o_v && (!(&cvr_bits)))
		cvr_bits <= cvr_bits + 1;

	reg	cvr_interesting;
	always @(*)
		cvr_interesting = f_past_valid && cvr_check && (&cvr_bits);

	//
	// Doesn't get reached inside 160 steps
	//
	// always @(posedge i_clk)
	//	cover($fell(r_busy) && !$past(i_reset) && (r_spd == SPD10M)
	//		&& cvr_interesting && ($past(o_d) > 8'h3));

	always @(posedge i_clk)
		cover($fell(r_busy) && !$past(i_reset) && (r_spd == SPD100M)
			&& cvr_interesting && ($past(o_d) > 8'h3));

	always @(posedge i_clk)
		cover($fell(r_busy) && !$past(i_reset) && (r_spd == SPD1G)
			&& cvr_interesting && ($past(o_d) > 8'h3));

`endif
endmodule
