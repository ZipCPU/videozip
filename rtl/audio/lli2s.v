////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/audio/lli2s.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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
module	lli2s (
		// {{{
		input	wire		i_mclk,	// Must be at 1024x BCLK freq
					i_clken, i_lren,
		input	wire	[3:0]	i_bdiv,
		output	reg		o_lrclk, o_bclk,
		output	reg		o_stb, o_chan,
		input	wire	[31:0]	i_dac,
		output	reg		o_dac,
		input	wire		i_adc,
		output	reg	[31:0]	o_adc
		// }}}
	);

	// Local declarations
	// {{{
	reg	[4:0]	b_cnt;
	reg		b_stb, b_neg, b_pos;

	reg	[4:0]	lr_cnt;
	reg		lr_stb;

	wire		w_stb;
	reg	[31:0]	r_dac, r_adc;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// MCLK
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Must be at 1024 the underlying sample rate.  Hence,
	// 49.152 MHz for 48  kHz samples and submultiples, or alternatively
	// 45.1584MHz for 44.1kHz and submultiples
	//
	// 49.152 MHz = 100MHz * (12/25) * (128 / 125)
	//            = (100MHz / 10) * (12/5) * (128 / 125)
	// 45.1584MHz = 100MHz * (14/25) * (28/25) * (18/25)
	//
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// BCLK
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// BCLK = Bit clock = fs*64, m_clk = 24.576MHz // 49.152MHz
	// i_bdiv =  1 --> 96kHz
	// i_bdiv =  2 --> 48kHz
	// i_bdiv =  3 --> 32kHz
	// i_bdiv =  4 --> 24kHz
	// i_bdiv =  6 --> 16kHz
	// i_bdiv =  8 --> 12kHz
	// i_bdiv = 12 -->  8kHz
	//
	// BCLK = Bit clock = fs*64, m_clk = 45.1584MHz
	// i_bdiv =  2 --> 44.1  kHz
	// i_bdiv =  4 --> 22.05 kHz
	// i_bdiv =  8 --> 11.025kHz
	//

	// b_cnt, b_stb
	// {{{
	initial	b_cnt = 0;
	initial	b_stb = 0;
	initial	b_pos = 0;
	initial	b_neg = 0;
	always @(posedge i_mclk)
	if (!i_clken)
	begin
		b_cnt <= 1;
		b_stb <= 0;
		b_neg <= 0;
		b_pos <= 0;
	end else begin
		b_cnt <= b_cnt + 1;

		if (b_cnt >= { i_bdiv, 1'b0 }-1)
			b_cnt <= 0;

		b_stb <= (b_cnt >= { i_bdiv, 1'b0 }-1);
		b_pos <= (b_cnt >= { i_bdiv, 1'b0 }-1) && !o_bclk;
		b_neg <= (b_cnt >= { i_bdiv, 1'b0 }-1) &&  o_bclk;
	end
`ifdef	FORMAL
	always @(*)
		assume(i_bdiv != 0);

	always @(posedge i_mclk)
	if (i_clken && $stable(i_bdiv))
	begin
		if (i_bdiv == 0)
		begin
			assert(b_cnt == 0);
		end else begin
			assert(b_cnt <= { i_bdiv, 1'b0 }-1);
		end
		assert(b_stb == (b_cnt == 0));
		assert(!b_pos || !b_neg);
		assert(b_stb == (b_pos || b_neg));
	end
`endif
	// }}}

	// o_bclk
	// {{{
	initial	o_bclk = 0;
	always @(posedge i_mclk)
	if (!i_clken)
		o_bclk <= 1'b0;
	else if (b_stb)
		o_bclk <= !o_bclk;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// LR-Clock
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Must be at desired sample rate (i.e. 96kHz or 48kHz)
	// The below code divides BCLK by 64, providing for 32 bits per each
	// of the left and right samples

	// lr_cnt
	// {{{
	initial	lr_cnt = 0;
	always @(posedge i_mclk)
	if (!i_lren || !i_clken)
		lr_cnt <= 0;
	else if (b_neg)
		lr_cnt <= lr_cnt + 1'b1;
	// }}}

	// lr_stb
	// {{{
	initial	lr_stb = 0;
	always @(posedge i_mclk)
	if (!i_lren || !i_clken)
		lr_stb <= 1'b0;
	else if (b_neg)
		lr_stb <= (lr_cnt == 5'h1e);
`ifdef	FORMAL
	always @(posedge i_mclk)
	if (i_clken && $past(i_lren && i_clken))
		assert(lr_stb == (lr_cnt == 5'h1f));
`endif
	// }}}

	// o_lrclk
	// {{{
	initial	o_lrclk = 0;
	always @(posedge i_mclk)
	if (!i_clken)
		o_lrclk <= 1'b0;
	else if (lr_stb && b_neg)
		o_lrclk <= !o_lrclk;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Data handling: O_DAC, O_ADC
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	w_stb = (lr_stb)&&(b_neg);

	initial	o_dac = 1'b0;
	initial	r_dac = 0;
	always @(posedge i_mclk)
	if (b_neg)
	begin
		if (lr_stb)
		begin
			r_dac <= { i_dac[30:0], 1'b0 };
			o_dac <= i_dac[31];
		end else begin
			r_dac <= { r_dac[30:0], 1'b0 };
			o_dac <= r_dac[31];
		end
	end

	initial	r_adc = 32'h0;
	always @(posedge i_mclk)
	if (b_pos)
		r_adc <= { r_adc[30:0], i_adc };

	initial	o_adc = 0;
	always @(posedge i_mclk)
	begin
		o_stb  <= w_stb   && i_clken;
		o_chan <= o_lrclk && i_clken;
		if (lr_stb && b_neg)
			o_adc <= r_adc;
		if (!i_clken)
			o_adc <= 0;
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
	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_mclk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!i_clken);

	////////////////////////////////////////////////////////////////////////
	//
	// Channel properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// 1. Everything is stable save on negedge BCLK
	// 1. 64 BCLK's per LRCLK, 32 high then 32 low

	always @(posedge i_mclk)
	if ((f_past_valid)&&(!$fell(o_bclk)))
	begin
		assume($stable(i_adc));
		assert($stable(o_adc));
		assert($stable(o_lrclk));
	end

	always @(*)
	if (b_neg)
		assert(o_bclk);
	else if (b_pos)
		assert(!o_bclk);

	always @(posedge i_mclk)
	if ((f_past_valid)&&($past(b_stb)))
		assert($changed(o_bclk));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	(* anyseq *)	reg [31:0]	fc_adc;
			reg [31:0]	fc_dac;

	// DAC path
	// {{{
	initial	fc_dac = 0;
	always @(posedge i_mclk)
	if (b_neg && lr_stb)
		fc_dac <= i_dac;

	always @(posedge i_mclk)
	if ((f_past_valid)&&(!$past(i_clken))&&(!$fell(o_bclk)))
		assert($stable(o_dac));

	always @(posedge i_mclk)
	if (f_past_valid && $past(i_clken))
	begin
		assert(o_dac == fc_dac[~lr_cnt]);
		case(lr_cnt)
		5'h00: assert(r_dac == { fc_dac[30:0], 1'h0 });
		5'h01: assert(r_dac == { fc_dac[29:0], 2'h0 });
		5'h02: assert(r_dac == { fc_dac[28:0], 3'h0 });
		5'h03: assert(r_dac == { fc_dac[27:0], 4'h0 });
		5'h04: assert(r_dac == { fc_dac[26:0], 5'h0 });
		5'h05: assert(r_dac == { fc_dac[25:0], 6'h0 });
		5'h06: assert(r_dac == { fc_dac[24:0], 7'h0 });
		5'h07: assert(r_dac == { fc_dac[23:0], 8'h0 });
		5'h08: assert(r_dac == { fc_dac[22:0], 9'h0 });
		5'h09: assert(r_dac == { fc_dac[21:0], 10'h0 });
		5'h0a: assert(r_dac == { fc_dac[20:0], 11'h0 });
		5'h0b: assert(r_dac == { fc_dac[19:0], 12'h0 });
		5'h0c: assert(r_dac == { fc_dac[18:0], 13'h0 });
		5'h0d: assert(r_dac == { fc_dac[17:0], 14'h0 });
		5'h0e: assert(r_dac == { fc_dac[16:0], 15'h0 });
		5'h0f: assert(r_dac == { fc_dac[15:0], 16'h0 });
		5'h10: assert(r_dac == { fc_dac[14:0], 17'h0 });
		5'h11: assert(r_dac == { fc_dac[13:0], 18'h0 });
		5'h12: assert(r_dac == { fc_dac[12:0], 19'h0 });
		5'h13: assert(r_dac == { fc_dac[11:0], 20'h0 });
		5'h14: assert(r_dac == { fc_dac[10:0], 21'h0 });
		5'h15: assert(r_dac == { fc_dac[ 9:0], 22'h0 });
		5'h16: assert(r_dac == { fc_dac[ 8:0], 23'h0 });
		5'h17: assert(r_dac == { fc_dac[ 7:0], 24'h0 });
		5'h18: assert(r_dac == { fc_dac[ 6:0], 25'h0 });
		5'h19: assert(r_dac == { fc_dac[ 5:0], 26'h0 });
		5'h1a: assert(r_dac == { fc_dac[ 4:0], 27'h0 });
		5'h1b: assert(r_dac == { fc_dac[ 3:0], 28'h0 });
		5'h1c: assert(r_dac == { fc_dac[ 2:0], 29'h0 });
		5'h1d: assert(r_dac == { fc_dac[ 1:0], 30'h0 });
		5'h1e: assert(r_dac == { fc_dac[ 0:0], 31'h0 });
		5'h1f: assert(r_dac == 32'h0);
		endcase
	end
	// }}}

	// ADC path
	// {{{
	always @(posedge i_mclk)
	if (f_past_valid && $past(i_clken) && !$changed(o_lrclk))
		assume($stable(fc_adc));

	always @(posedge i_mclk)
	if (f_past_valid && $past(i_clken) && !$fell(o_bclk))
	begin
		assert($stable(lr_cnt));
		assume($stable(i_adc));
	end

	always @(posedge i_mclk)
		assume(i_adc == fc_adc[~lr_cnt]);

	always @(posedge i_mclk)
	if (f_past_valid && o_stb)
		assert(o_adc == $past(fc_adc));
	else case(lr_cnt + o_bclk)
	6'h00: begin end
	6'h01: assert(r_adc[ 0:0] == fc_adc[31]);
	6'h02: assert(r_adc[ 1:0] == fc_adc[31:30]);
	6'h03: assert(r_adc[ 2:0] == fc_adc[31:29]);
	6'h04: assert(r_adc[ 3:0] == fc_adc[31:28]);
	6'h05: assert(r_adc[ 4:0] == fc_adc[31:27]);
	6'h06: assert(r_adc[ 5:0] == fc_adc[31:26]);
	6'h07: assert(r_adc[ 6:0] == fc_adc[31:25]);
	6'h08: assert(r_adc[ 7:0] == fc_adc[31:24]);
	6'h09: assert(r_adc[ 8:0] == fc_adc[31:23]);
	6'h0a: assert(r_adc[ 9:0] == fc_adc[31:22]);
	6'h0b: assert(r_adc[10:0] == fc_adc[31:21]);
	6'h0c: assert(r_adc[11:0] == fc_adc[31:20]);
	6'h0d: assert(r_adc[12:0] == fc_adc[31:19]);
	6'h0e: assert(r_adc[13:0] == fc_adc[31:18]);
	6'h0f: assert(r_adc[14:0] == fc_adc[31:17]);
	6'h10: assert(r_adc[15:0] == fc_adc[31:16]);
	6'h11: assert(r_adc[16:0] == fc_adc[31:15]);
	6'h12: assert(r_adc[17:0] == fc_adc[31:14]);
	6'h13: assert(r_adc[18:0] == fc_adc[31:13]);
	6'h14: assert(r_adc[19:0] == fc_adc[31:12]);
	6'h15: assert(r_adc[20:0] == fc_adc[31:11]);
	6'h16: assert(r_adc[21:0] == fc_adc[31:10]);
	6'h17: assert(r_adc[22:0] == fc_adc[31: 9]);
	6'h18: assert(r_adc[23:0] == fc_adc[31: 8]);
	6'h19: assert(r_adc[24:0] == fc_adc[31: 7]);
	6'h1a: assert(r_adc[25:0] == fc_adc[31: 6]);
	6'h1b: assert(r_adc[26:0] == fc_adc[31: 5]);
	6'h1c: assert(r_adc[27:0] == fc_adc[31: 4]);
	6'h1d: assert(r_adc[28:0] == fc_adc[31: 3]);
	6'h1e: assert(r_adc[29:0] == fc_adc[31: 2]);
	6'h1f: assert(r_adc[30:0] == fc_adc[31: 1]);
	6'h20: assert(r_adc[31:0] == fc_adc[31: 0]);
	default: begin end
	endcase
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover
	// {{{

	always @(*)
	if (f_past_valid && o_stb)
		cover(o_adc == 32'h12345678);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless assumptions"
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	(* anyconst *)	reg	[3:0]	f_bdiv;

	always @(*)
		assume(i_bdiv == f_bdiv);

	always @(*)
		assume(i_clken == f_past_valid);
	always @(*)
		assume(i_lren == i_clken);

	// }}}
`endif
// }}}
endmodule
