////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/sdspi/sdtxframe.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Given a frame of data from memory, formats it for sending to
//		the front end.
//
// Comments:
//	This implementation really needs a means of stopping the SD clock if
//	the incoming data isn't yet ready.  Although the command controller
//	doesn't (yet) use such a feature, it could be quite valuable in the
//	future when working with a stream-based DMA.  (Perhaps it needs to be
//	made as a parameter?)
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
`timescale 1ns/1ps
`default_nettype	none
// }}}
module	sdtxframe #(
		// {{{
		parameter		NCRC = 16,
		// OPT_SERDES=1 delays the invocation of tristate by a clock
		// cycle.  This is in an attempt to match Xilinx's 8x SERDES.
		parameter [0:0]		OPT_SERDES = 1'b0,
		parameter [0:0]		OPT_CRCTOKEN = 1'b0,
		parameter [NCRC-1:0]	CRC_POLYNOMIAL  = 16'h1021
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire	[7:0]		i_cfg_spd,
		input	wire	[1:0]		i_cfg_width,
		input	wire			i_cfg_ddr,
		input	wire			i_cfg_pp,
		input	wire			i_cfg_expect_ack,
		//
		input	wire			i_cfg_clk90,
		input	wire	[7:0]		i_ckwide,
		//
		input	wire			i_en, i_ckstb, i_hlfck,
		//
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[31:0]		S_DATA,
		input	wire			S_LAST,
		//
		output	wire			tx_valid,
		// input wire			tx_ready,
		output	wire	[31:0]		tx_data,
		output	wire			tx_tristate,
		//
		input	wire			i_crcack,
		input	wire			i_crcnak,
		output	wire			o_done,
		output	wire			o_err,
		output	wire			o_ercode
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	P_IDLE = 2'b00,
				P_DATA = 2'b01,
				P_CRC  = 2'b10,
				P_LAST = 2'b11;

	localparam [1:0]	WIDTH_1W = 2'b00,
				WIDTH_4W = 2'b01,
				WIDTH_8W = 2'b10;

	localparam [1:0]	P_1D = 2'b00,
				P_2D = 2'b01,
				P_4D = 2'b10;

	reg		cfg_ddr, cfg_pp;
	reg	[1:0]	cfg_width, cfg_period;


	wire		start_packet;
	reg		pre_valid;
	reg	[1:0]	pstate;
	wire		pre_ready;
	reg	[31:0]	pre_data;
	reg	[3:0]	pre_count;


	integer		ik, jk;
	reg	[NCRC- 1:0]	crc_1w_reg;
	reg	[NCRC* 2-1:0]	di_crc_2w, nxt_crc_2w, new_crc_2w, crc_2w_reg;
	reg	[NCRC* 4-1:0]	di_crc_4w, nxt_crc_4w, new_crc_4w, crc_4w_reg;
	reg	[NCRC* 8-1:0]	di_crc_8w, nxt_crc_8w, new_crc_8w, crc_8w_reg;
	reg	[NCRC*16-1:0]	di_crc_8d, nxt_crc_8d, new_crc_8d, crc_8d_reg;

	reg		ck_valid, ck_tristate, ck_stop_bit;
	reg		r_tristate;

	reg	[4:0]	ck_counts;
	reg	[31:0]	ck_data, ck_sreg;

	reg		r_done;
	reg	[3:0]	r_timeout;

	// }}}
	// Steps: #1, Packetizer: breaks incoming signal into wires
	// 	#2, add CRC
	//	#3, split across clocks
	//
	////////////////////////////////////////////////////////////////////////
	//
	// Configuration
	// {{{
	initial	cfg_period = 2'b00;
	always @(posedge i_clk)
	if (i_reset || !OPT_SERDES)
		cfg_period <= P_1D;
	else if (pstate == P_IDLE)
	begin
		if (i_cfg_ddr && i_cfg_spd == 0)
			cfg_period <= P_4D;	// Four data periods / clk
		else if ((i_cfg_ddr && i_cfg_spd == 1)
			||(!i_cfg_ddr && i_cfg_spd == 0))
			cfg_period <= P_2D;	// Two data periods / clk
		else
			cfg_period <= P_1D;	// One data period / clk
	end

	always @(posedge i_clk)
	if (i_reset)
		cfg_width <= WIDTH_1W;
	else if (pstate == P_IDLE)
		cfg_width <= i_cfg_width;

	always @(posedge i_clk)
	if (i_reset)
		cfg_pp <= 1'b0;
	else if (pstate == P_IDLE)
		cfg_pp <= i_cfg_pp;

	always @(posedge i_clk)
	if (i_reset)
		cfg_ddr <= 1'b0;
	else if (pstate == P_IDLE)
		cfg_ddr <= i_cfg_ddr;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Packetizer: Add CRC(s) to the packet
	// {{{

	assign	start_packet = i_en && S_VALID && i_ckstb && !tx_valid && !ck_valid;
	initial	pstate    = P_IDLE;
	initial	pre_valid = 1'b0;
	initial	pre_data  = {(32){1'b1}};
	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		pstate    <= P_IDLE;
		pre_valid <= 1'b0;
		pre_data  <= {(32){1'b1}};
		// }}}
	end else case(pstate)
	P_IDLE: begin
		// {{{
		pstate <= P_IDLE;
		pre_valid <= 0;
		pre_data <= (S_VALID) ? S_DATA : {(32){1'b1}};
		if (start_packet)
		begin
			pstate    <= (S_LAST) ? P_CRC : P_DATA;
			pre_valid <= 1;
		end end
		// }}}
	P_DATA: if (S_VALID && S_READY)
		// {{{
		begin
			pstate <= P_DATA;
			pre_valid <= 1;
			pre_data <= S_DATA;

			if (S_LAST)
				pstate <= P_CRC;
		end
		// }}}
	P_CRC: if (pre_ready)
		// {{{
		begin
			pre_valid <= 1'b1;
			if (pre_count == 0)
				pstate <= P_LAST;

			case(cfg_width)
			WIDTH_1W: if (cfg_ddr)
					pre_data <= crc_2w_reg[NCRC*2-1:0];
				else
				pre_data <= { crc_1w_reg[NCRC-1:0], 16'hffff };
			WIDTH_4W: if (cfg_ddr)
				pre_data <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
				else
				pre_data <= crc_4w_reg[4*NCRC-1:4*NCRC-32];
			WIDTH_8W: if (cfg_ddr)
				pre_data <= crc_8d_reg[16*NCRC-1:16*NCRC-32];
				else
				pre_data <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
			default: pre_data  <= crc_8w_reg[8*NCRC-1:8*NCRC-32];
			endcase
		end
		// }}}
	P_LAST: begin
		if (pre_ready)
		begin
			pre_valid <= 0;
			pre_data <= {(32){1'b1}};
		end

		if (!tx_valid)
			pstate <= P_IDLE;
		end
	endcase

	initial	pre_count = 0;
	always @(posedge i_clk)
	if (i_reset)
		pre_count <= 0;
	else if (pstate == P_DATA || pstate == P_IDLE)
	begin
		// pre_count =
		//	(SDR)	16bits / wire / 32
		//	(DDR)	32bits / wire / 32
		case(cfg_width)
		WIDTH_1W: pre_count <= 0;
		WIDTH_4W: pre_count <= (cfg_ddr) ? 3 : 1;
		default: // WIDTH_8W
			pre_count <= (cfg_ddr) ? 7:3;
		endcase
	end else if (pre_ready && pre_count != 0)
		pre_count <= pre_count - 1;

	assign	S_READY = pre_ready && (pstate == P_DATA || pstate == P_IDLE);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC calculation
	// {{{

	// di_crc*, new_crc*, next_crc*: Advance CRC calculations combinatorialy
	// {{{
	always @(*)
	begin
		// Notes:
		// {{{
		// Why the following monstrosity?  So we can read data out
		// directly into the shift register(s).  However, the shift
		// register(s) are not sorted by rail, hence all the work
		// below to first sort them by rail, adjust the CRC, then
		// sort them back, etc.
		//
		// The good news is that, inspite of all the tortured pain
		// below, it's primarily just wire assignments and
		// rearrangements.  The logic itself is either a shift, or
		// (for 1-4 bits per CRC per step), a XOR reduction of up
		// to 20 incoming bits.
		// }}}

		// Pre-load the CRC fills
		// {{{
		for(ik=0; ik<NCRC; ik=ik+1)
		begin
			for(jk=0; jk<2; jk=jk+1)
				di_crc_2w[jk*NCRC+ik] = crc_2w_reg[ik*2+jk];

			for(jk=0; jk<4; jk=jk+1)
				di_crc_4w[jk*NCRC+ik] = crc_4w_reg[ik*4+jk];

			for(jk=0; jk<8; jk=jk+1)
				di_crc_8w[jk*NCRC+ik] = crc_8w_reg[ik*8+jk];

			for(jk=0; jk<16; jk=jk+1)
				di_crc_8d[jk*NCRC+ik] = crc_8d_reg[ik*16+jk];
		end
		// }}}

		// Advance the CRCs based on S_DATA
		// {{{
		for(ik=0; ik<2; ik=ik+1)
		begin
			new_crc_2w[ik*NCRC +: NCRC] =
				APPLYCRC16(di_crc_2w[ik*NCRC +: NCRC],
			  		{ S_DATA[30+ik],S_DATA[28+ik],
						S_DATA[26+ik],S_DATA[24+ik],
						S_DATA[22+ik],S_DATA[20+ik],
						S_DATA[18+ik],S_DATA[16+ik],
						S_DATA[14+ik],S_DATA[12+ik],
						S_DATA[10+ik],S_DATA[ 8+ik],
						S_DATA[ 6+ik],S_DATA[ 4+ik],
						S_DATA[ 2+ik],S_DATA[   ik] });
		end

		for(ik=0; ik<4; ik=ik+1)
		begin
			new_crc_4w[ik*NCRC +: NCRC] =
				APPLYCRC8(di_crc_4w[ik*NCRC +: NCRC],
			  		{ S_DATA[28+ik],S_DATA[24+ik],
						S_DATA[20+ik],S_DATA[16+ik],
						S_DATA[12+ik],S_DATA[ 8+ik],
						S_DATA[ 4+ik],S_DATA[   ik] });
		end

		for(ik=0; ik<8; ik=ik+1)
		begin
			new_crc_8w[ik*NCRC +: NCRC] =
				APPLYCRC4(di_crc_8w[ik*NCRC +: NCRC],
			  		{ S_DATA[24+ik], S_DATA[16+ik],
						S_DATA[8+ik], S_DATA[ik] });
		end

		for(ik=0; ik<16; ik=ik+1)
		begin
			new_crc_8d[ik*NCRC +: NCRC] =
				APPLYCRC2(di_crc_8d[ik*NCRC +: NCRC],
			  		{ S_DATA[16+ik], S_DATA[ik] });
		end
		// }}}

		// Order the bits to place the results back in line
		// {{{
		for(ik=0; ik<NCRC; ik=ik+1)
		begin
			for(jk=0; jk<2; jk=jk+1)
				nxt_crc_2w[ik*2+jk] = new_crc_2w[jk*NCRC+ik];
			for(jk=0; jk<4; jk=jk+1)
				nxt_crc_4w[ik*4+jk] = new_crc_4w[jk*NCRC+ik];
			for(jk=0; jk<8; jk=jk+1)
				nxt_crc_8w[ik*8+jk] = new_crc_8w[jk*NCRC+ik];
			for(jk=0; jk<16; jk=jk+1)
				nxt_crc_8d[ik*16+jk] = new_crc_8d[jk*NCRC+ik];
		end
		// }}}
	end
	// }}}

	// crc_*_reg: Advance CRC calculations sequentially w/ new data
	// {{{
	always @(posedge i_clk)
	if (i_reset || (!i_en && !tx_valid))
	begin
		crc_1w_reg <= 0;
		crc_2w_reg <= 0;
		crc_4w_reg <= 0;
		crc_8w_reg <= 0;
		crc_8d_reg <= 0;
	end else if (S_VALID && S_READY)
	begin
		crc_1w_reg <= {(NCRC   ){1'b1}};
		crc_2w_reg <= {(NCRC* 2){1'b1}};
		crc_4w_reg <= {(NCRC* 4){1'b1}};
		crc_8w_reg <= {(NCRC* 8){1'b1}};
		crc_8d_reg <= {(NCRC*16){1'b1}};

		case(cfg_width)
		WIDTH_1W: if (cfg_ddr)
				crc_2w_reg <= nxt_crc_2w;
			else
				crc_1w_reg <= APPLYCRC32(crc_1w_reg, S_DATA);
		WIDTH_4W: if (cfg_ddr)
				crc_8w_reg <= nxt_crc_8w;
			else
				crc_4w_reg <= nxt_crc_4w;
		WIDTH_8W: if (cfg_ddr)
				crc_8d_reg <= nxt_crc_8d;
			else
				crc_8w_reg <= nxt_crc_8w;
		default: begin end
		endcase
	end else if (i_ckstb && pstate != P_IDLE && pstate != P_DATA && ck_counts == 0)
	begin
		crc_1w_reg <= {(NCRC){1'b1}};
		crc_2w_reg <= {(2*NCRC){1'b1}};
		crc_4w_reg <= { crc_4w_reg[ 4*NCRC-32-1:0], 32'hffff_ffff };
		crc_8w_reg <= { crc_8w_reg[ 8*NCRC-32-1:0], 32'hffff_ffff };
		crc_8d_reg <= { crc_8d_reg[16*NCRC-32-1:0], 32'hffff_ffff };
	end
	// }}}

	function automatic [NCRC-1:0] STEPCRC(input [NCRC-1:0] prior,
		// {{{
				input i_bit);
	begin
		if (prior[NCRC-1] ^ i_bit)
			STEPCRC = { prior[NCRC-2:0], 1'b0 } ^ CRC_POLYNOMIAL;
		else
			STEPCRC = { prior[NCRC-2:0], 1'b0 };
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC32(input [NCRC-1:0] prior,
		// {{{
			input [31:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<32; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[31-ck]);

		APPLYCRC32 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC16(input [NCRC-1:0] prior,
		// {{{
			input [15:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<16; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[15-ck]);
		APPLYCRC16 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC8(input [NCRC-1:0] prior,
		// {{{
			input [7:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<8; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[7-ck]);
		APPLYCRC8 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC4(input [NCRC-1:0] prior,
		// {{{
			input [3:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<4; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[3-ck]);
		APPLYCRC4 = fill;
	end endfunction
	// }}}

	function automatic [NCRC-1:0] APPLYCRC2(input [NCRC-1:0] prior,
		// {{{
			input [1:0] i_crc_data);
		integer		ck;
		reg	[NCRC-1:0]	fill;
	begin
		fill = prior;
		for(ck=0; ck<2; ck=ck+1)
			fill = STEPCRC(fill, i_crc_data[1-ck]);
		APPLYCRC2 = fill;
	end endfunction
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Clock divider, data shift register
	// {{{

	// ck_valid
	// {{{
	initial	ck_valid = 0;
	initial	ck_stop_bit = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		ck_valid <= 0;
		ck_stop_bit <= 1'b0;
	end else if (start_packet)
	begin
		// Start us one clock cycle early with a single start bit
		ck_valid <= 1;
		ck_stop_bit <= 1'b1;	// Need a stop bit
	end else if (i_ckstb && ck_counts == 0)
	begin
		ck_valid    <= pre_valid || ck_stop_bit;
		ck_stop_bit <= pre_valid;
	end
	// }}}

	initial	ck_counts = 0;
	initial	ck_sreg = -1;
	initial	ck_data = -1;
	always @(posedge i_clk)
	if (i_reset) // pstate == P_IDLE)
	begin
		// {{{
		ck_sreg  <= {(32){1'b1}};
		ck_data  <= {(32){1'b1}};
		ck_counts<= 0;
		// }}}
	end else if (i_ckstb && pre_valid && ck_counts == 0) // && tx_ready
	begin // Load the shift registers
		case(cfg_period)
		P_1D: begin // One clock period of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[30: 0], 1'b1 };
				ck_data <= { (4){7'h7f, pre_data[31] } };
				// In the case of the 1b CRC, we only need
				// 16 clock cycles, not 32.
				ck_counts <= (!cfg_ddr && pstate == P_LAST) ? 15: 31;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[27: 0], 4'hf };
				ck_data <= { (4){ 4'hf, pre_data[31:28] } };
				ck_counts <= 7;
				end
			default: begin // WIDTH_8W
				ck_sreg <= { pre_data[23: 0], 8'hff };
				ck_data <= { (4){pre_data[31:24] } };
				ck_counts <= 3;
				end
			endcase end
			// }}}
		P_2D: begin // Two clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[29: 0], 2'b11 };
				ck_data <= { {(2){7'h7f, pre_data[31] }},
						{(2){7'h7f, pre_data[30] }} };
				ck_counts <= 15;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[23: 0], 8'hff };
				ck_data <= { {(2){4'hf, pre_data[31:28] }},
						{(2){4'hf, pre_data[27:24] }} };
				ck_counts <= 3;
				end
			default: begin // WIDTH_8W
				ck_sreg <= { pre_data[15: 0], 16'hffff };
				ck_data <= { {(2){pre_data[31:24] }},
						{(2){pre_data[23:16]}} };
				ck_counts <= 1;
				end
			endcase end
			// }}}
		default: begin // Four clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { pre_data[27: 0], 4'hf };
				ck_data <= { 7'h7f, pre_data[31],
						7'h7f, pre_data[30],
						7'h7f, pre_data[29],
						7'h7f, pre_data[28] };
				ck_counts <= 7;
				end
			WIDTH_4W: begin
				ck_sreg <= { pre_data[15: 0], 16'hffff };
				ck_data <= { 4'hf, pre_data[31:28],
					4'hf, pre_data[27:24],
					4'hf, pre_data[23:20],
					4'hf, pre_data[19:16] };
				ck_counts <= 1;
				end
			default: begin // WIDTH_8W
				ck_sreg <= {(32){1'b1}};
				ck_data <= pre_data;
				ck_counts <= 0;
				end
			endcase end
			// }}}
		endcase
	end else if ((i_ckstb || (i_hlfck && cfg_ddr)) && ck_counts > 0)
	begin // Drain the shift registers
		ck_counts <= ck_counts - 1;
		case(cfg_period)
		P_1D: begin // One clock period of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[30: 0], 1'b1 };
				ck_data <= { (4){7'h7f, ck_sreg[31] }};
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[27: 0], 4'hf };
				ck_data <= { (4){4'hf, ck_sreg[31:28] } };
				end
			default: begin // WIDTH_8W
				ck_sreg <= { ck_sreg[23: 0], 8'hff };
				ck_data <= { (4){ck_sreg[31:24] } };
				end
			endcase end
			// }}}
		P_2D: begin // Two clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[29: 0], 2'b11 };
				ck_data <= { {(2){7'h7f, ck_sreg[31] }},
						{(2){7'h7f, ck_sreg[30] }} };
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[23: 0], 8'hff };
				ck_data <= { {(2){4'hf, ck_sreg[31:28] }},
						{(2){4'hf, ck_sreg[27:24] }} };
				end
			default: begin // WIDTH_8W
				ck_sreg <= { ck_sreg[15: 0], 16'hffff };
				ck_data <= { {(2){ck_sreg[31:24] }},
						{(2){ck_sreg[23:16]}} };
				end
			endcase end
			// }}}
		default: begin // Four clock periods of data
			// {{{
			case(cfg_width)
			WIDTH_1W: begin
				ck_sreg <= { ck_sreg[27: 0], 4'hf };
				ck_data <= { 7'h7f, ck_sreg[31],
						7'h7f, ck_sreg[30],
						7'h7f, ck_sreg[29],
						7'h7f, ck_sreg[28] };
				end
			WIDTH_4W: begin
				ck_sreg <= { ck_sreg[15: 0], 16'hffff };
				ck_data <= { 4'hf, ck_sreg[31:28],
					4'hf, ck_sreg[27:24],
					4'hf, ck_sreg[23:20],
					4'hf, ck_sreg[19:16] };
				end
			default: begin // WIDTH_8W
				ck_sreg <= {(32){1'b1}};
				ck_data <= ck_sreg;
				end
			endcase end
			// }}}
		endcase
	end else if (i_ckstb && ck_counts == 0)
	begin
		// Fully idle
		ck_data  <= -1;
		ck_sreg  <= -1;

		ck_counts <= (start_packet && i_cfg_ddr && !i_hlfck) ? 1:0;

		if (start_packet)	// Implies i_ckstb
		case(cfg_period)
		2'b00: begin // One data period / clock
			case(cfg_width)
			WIDTH_1W: ck_data  <= {(4){ 8'hfe }};
			WIDTH_4W: ck_data  <= {(4){ 8'hf0 }};
			default:  ck_data  <= {(4){ 8'h00 }};
			endcase end
		2'b01: begin // Two data periods / clock
			// {{{
			if (cfg_ddr)
			begin
				// One pedge, one negedge
				case(cfg_width)
				WIDTH_1W: ck_data  <= {(4){ 8'hfe }};
				WIDTH_4W: ck_data  <= {(4){ 8'hf0 }};
				default:  ck_data  <= {(4){ 8'h00 }};
				endcase
			end else begin
				// Two posedges, so only the second gets the
				// start bits
				case(cfg_width)
				WIDTH_1W: ck_data  <= { {(2){8'hff}}, {(2){8'hfe}} };
				WIDTH_4W: ck_data  <= { {(2){8'hff}}, {(2){8'hf0}} };
				default:  ck_data  <= { {(2){8'hff}}, {(2){8'h00}} };
				endcase
			end end
			// }}}
		default: begin // 4 data periods / clock, DDR
			// pedge, nedge, pedge, nedge, so the last two
			// get the start bit
			case(cfg_width)
			WIDTH_1W: ck_data  <= { {(2){8'hff}}, {(2){8'hfe}} };
			WIDTH_4W: ck_data  <= { {(2){8'hff}}, {(2){8'hf0}} };
			default:  ck_data  <= { {(2){8'hff}}, {(2){8'h00}} };
			endcase end
		endcase
	end

	initial {r_tristate, ck_tristate } = 2'h3;
	always @(posedge i_clk)
	if (i_reset) // pstate == P_IDLE)
	begin
		ck_tristate <= 1'b1;
		r_tristate <= 1'b1;
	end else if (i_ckstb && pre_valid && ck_counts == 0) // && tx_ready
	begin
		if (cfg_pp || cfg_period != P_1D)
		begin
			ck_tristate <= 1'b0;
			r_tristate <= 1'b0;
		end else case(cfg_width) // One clock period of data
		WIDTH_1W: begin
			ck_tristate <= pre_data[31];
			r_tristate <= pre_data[31] && (!OPT_SERDES || ck_tristate);
			end
		WIDTH_4W: begin
			ck_tristate <= (&pre_data[31:28]);
			r_tristate <= (&pre_data[31:28]) && (!OPT_SERDES || ck_tristate);
			end
		default:  begin
			ck_tristate <= (&pre_data[31:24]);
			r_tristate <= (&pre_data[31:24]) && (!OPT_SERDES || ck_tristate);
			end
		endcase
	end else if ((i_ckstb || (i_hlfck && cfg_ddr)) && ck_counts > 0)
	begin
		if (cfg_pp || cfg_period != P_1D)
		begin
			ck_tristate <= 1'b0;
			r_tristate <= 1'b0;
		end else case(cfg_width) // One clock period of data
		WIDTH_1W: begin
			ck_tristate <= ck_sreg[31];
			r_tristate <= ck_sreg[31] && (!OPT_SERDES || ck_tristate);
			end
		WIDTH_4W: begin
			ck_tristate <= (&ck_sreg[31:28]);
			r_tristate <= (&ck_sreg[31:28]) && (!OPT_SERDES || ck_tristate);
			end
		default:  begin
			ck_tristate <= (&ck_sreg[31:24]);
			r_tristate <= (&ck_sreg[31:24]) && (!OPT_SERDES || ck_tristate);
			end
		endcase
	end else if (i_ckstb && ck_counts == 0)
	begin
		ck_tristate <= 1'b1;
		r_tristate <= (!OPT_SERDES || ck_tristate);
		if (start_packet)
		begin
			ck_tristate <= 1'b0;
			r_tristate <= 1'b0;
		end
	end else
		r_tristate <= ck_tristate;

	assign	pre_ready = (ck_counts == 0) && i_ckstb; // && tx_ready;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Final outputs
	// {{{
	assign	tx_valid = ck_valid;
	// assign ck_ready = (i_ckstb || (i_hlfck && cfg_ddr)); // && tx_ready;
	assign	tx_data  = ck_data;
	assign	tx_tristate = r_tristate;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Status feedback
	// {{{

	// r_timeout
	// {{{
	// Insist on at least 10 clocks (2 + CRC) after any transmission before
	// declaring ourselves done.  The eMMC specification requires at least
	// 2 such clocks, together with the number of clocks required for an
	// ACK/NACK sequence (5).  Here, we round that number up to 15 for good
	// measure.
	initial	r_timeout = (OPT_CRCTOKEN) ? 4'd15 : 4'h0;
	always @(posedge i_clk)
	if (!OPT_CRCTOKEN)
		r_timeout <= 0;
	else if (i_reset || S_VALID || tx_valid || !i_en)
	begin
		r_timeout <= 15;
	end else if (i_ckstb && (r_timeout != 0))
		r_timeout <= r_timeout - 1;
	// }}}

	// o_done
	// {{{
	initial	r_done = 1'b0;
	always @(posedge i_clk)
	if (i_reset || S_VALID || tx_valid || !i_en)
		r_done <= 1'b0;
	else if (!r_done && ((i_ckstb && (!OPT_CRCTOKEN || r_timeout <= 1))
			|| i_crcack || i_crcnak))
		// Once set, r_done will stay set until i_en drops
		r_done <= 1'b1;

	assign	o_done = r_done;
	// }}}

	// o_err, o_ercode
	// {{{
	generate if (OPT_CRCTOKEN)
	begin : GEN_CRCERR
		reg	r_ackd, r_err, r_ercode;

		initial	r_ackd = 1'b0;
		always @(posedge i_clk)
		if (i_reset || (i_en && S_VALID) || tx_valid || !i_en)
			r_ackd <= 1'b0;
		else if (!r_done && i_crcack)
			r_ackd <= 1'b1;

		initial	{ r_err, r_ercode } = 2'b00;
		always @(posedge i_clk)
		if (i_reset || (i_en && S_VALID) || tx_valid || !i_en)
		begin
			{ r_err, r_ercode } <= 2'b00;
		end else if (i_en && !r_done && !o_err && !r_ackd)
		begin
			if (r_timeout <= 1 && i_cfg_expect_ack)
				{ r_err, r_ercode } <= 2'b10;
			if (i_crcnak && !i_crcack)
				{ r_err, r_ercode } <= 2'b11;
		end

		assign	{ o_err, o_ercode } = { r_err, r_ercode };
	end else begin : NO_CRCTOKEN
		assign	{ o_err, o_ercode } = 2'b00;

		// Verilator lint_off UNUSED
		wire	unused_token;
		assign	unused_token = &{ 1'b0, i_cfg_expect_ack };
		// Verilator lint_on  UNUSED
	end endgenerate
	// }}}

	// }}}

	//
	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, i_ckwide, i_cfg_clk90 };
	// verilator lint_on  UNUSED
	// verilator coverage_on
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
// Formal properties for this module are maintained elsewhere
`endif	// FORMAL
// }}}
endmodule

