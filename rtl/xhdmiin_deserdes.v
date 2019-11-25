////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	xhdmiin_deserdes.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
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
module	xhdmiin_deserdes(i_clk, i_hsclk,
		i_ce, i_delay, o_delay,
		i_hs_wire, o_wire, o_word);
	parameter	DELAYSRC = "IDATAIN", IOBDELAY="IFD";
	input	wire		i_clk;
	input	wire		i_hsclk;
	input	wire		i_ce;
	input	wire	[4:0]	i_delay;
	output	wire	[4:0]	o_delay;
	input	wire		i_hs_wire;
	output	wire		o_wire;
	output	reg	[9:0]	o_word;

	wire	[5:0]	ignored_data;
	wire	[1:0]	master_to_slave;
	wire		ignored_output_hi;

	wire	w_hs_delayed_wire, w_hs_wire;
	wire	[9:0]	w_word;

	wire		async_reset;
	reg	[2:0]	reset_pipe;
	always @(posedge i_clk, negedge i_ce)
		if (!i_ce)
			reset_pipe[2:0] <= 3'h7;
		else
			reset_pipe[2:0] <= { reset_pipe[1:0], 1'b0 };
	assign	async_reset = reset_pipe[2];

	wire		lcl_ce;
	reg	[1:0]	syncd_ce;
	always @(posedge i_clk)
		syncd_ce <= { syncd_ce[0], i_ce };
	assign	lcl_ce = syncd_ce[1];

	generate
	if (IOBDELAY == "NONE")
	begin

		assign w_hs_wire         = i_hs_wire;
		assign w_hs_delayed_wire = 1'b0;

	end else begin

		assign w_hs_wire = 1'b0;

		IDELAYE2	#(
			.CINVCTRL_SEL("FALSE"),
			.DELAY_SRC(DELAYSRC),
			.HIGH_PERFORMANCE_MODE("TRUE"),
			.IDELAY_TYPE("VAR_LOAD")
			) delay(
				.C(i_clk), 
				.CE(1'b1),
				.CINVCTRL(1'b0),
				//
				.CNTVALUEIN(i_delay),
				.CNTVALUEOUT(o_delay),
				.LD(1'b1),
				.LDPIPEEN(1'b0),
				.REGRST(1'b0),
				.DATAIN(),
				.DATAOUT(w_hs_delayed_wire),
				.INC(1'b0),
				.IDATAIN(i_hs_wire));

	end endgenerate

	ISERDESE2	#(
		.SERDES_MODE("MASTER"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY(IOBDELAY),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		) lowserdes(
			.BITSLIP(1'b0),
			.CE1(lcl_ce), .CE2(),
			.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
			.CLKDIV(i_clk), .CLKDIVP(1'b0),
			.D(w_hs_wire), .DDLY(w_hs_delayed_wire), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
			.O(o_wire), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
			.Q1(w_word[0]),
			.Q2(w_word[1]),
			.Q3(w_word[2]),
			.Q4(w_word[3]),
			.Q5(w_word[4]),
			.Q6(w_word[5]),
			.Q7(w_word[6]),
			.Q8(w_word[7]),
			.RST(async_reset),
			.SHIFTIN1(1'h0), .SHIFTIN2(1'h0),
			.SHIFTOUT1(master_to_slave[0]), .SHIFTOUT2(master_to_slave[1])
		);

	ISERDESE2	#(
		.SERDES_MODE("SLAVE"),
		//
		.DATA_RATE("DDR"),
		.DATA_WIDTH(10),
		.INTERFACE_TYPE("NETWORKING"),
		.IOBDELAY("NONE"),
		//
		.NUM_CE(1),
		.INIT_Q1(1'b0), .INIT_Q2(1'b0),
		.INIT_Q3(1'b0), .INIT_Q4(1'b0),
		.SRVAL_Q1(1'b0), .SRVAL_Q2(1'b0),
		.SRVAL_Q3(1'b0), .SRVAL_Q4(1'b0),
		.DYN_CLKDIV_INV_EN("FALSE"),
		.DYN_CLK_INV_EN("FALSE"),
		.OFB_USED("FALSE")
		) hiserdes(
			.BITSLIP(1'b0),
			.CE1(lcl_ce), .CE2(),
			.CLK(i_hsclk), .CLKB(!i_hsclk),	// HS clocks
			.CLKDIV(i_clk), .CLKDIVP(1'b0),
			.D(), .DDLY(), .DYNCLKDIVSEL(1'b0), .DYNCLKSEL(1'b0),
			.O(ignored_output_hi), .OCLK(1'b0), .OCLKB(1'b0), .OFB(1'b0),
			.Q1(),
			.Q2(),
			.Q3(w_word[8]),
			.Q4(w_word[9]),
			.Q5(),
			.Q6(),
			.Q7(),
			.Q8(),
			// .Q7(w_word[8]),
			// .Q8(w_word[9]),
			.RST(async_reset),
			.SHIFTIN1(master_to_slave[0]), .SHIFTIN2(master_to_slave[1]),
			.SHIFTOUT1(), .SHIFTOUT2()
		);

	// Any ISERDESE2 input is shifted by two clocks.  (See the ISERDESE2
	// latencies in the Artix-7 SelectI/O resources guide).  Hence, to undo
	// this, we need to shift our result by 8 clocks.  If the first bit
	// shifted in is w_word[9], and if we delay the whole word by r_word,
	// we get a series:
	//
	//	r_word[9:0], w_word[9:0]
	//
	// which we delay by eight clocks to get
	//
	// r_word[1:0], w_word[9:2]
	//
	wire	[9:0]	w_brev;
	assign	w_brev[9] = w_word[0];
	assign	w_brev[8] = w_word[1];
	assign	w_brev[7] = w_word[2];
	assign	w_brev[6] = w_word[3];
	assign	w_brev[5] = w_word[4];
	assign	w_brev[4] = w_word[5];
	assign	w_brev[3] = w_word[6];
	assign	w_brev[2] = w_word[7];
	assign	w_brev[1] = w_word[8];
	assign	w_brev[0] = w_word[9];

	wire	[9:0]	w_use_this_word;
	assign	w_use_this_word = w_word; // w_brev;

	localparam	DLY = 0;
	generate if (DLY != 0)
	begin
		reg	[(DLY-1):0]	r_word;
		always @(posedge i_clk)
			r_word <= w_use_this_word[(DLY-1):0];
		always @(posedge i_clk)
			o_word <= { r_word[(DLY-1):0],w_use_this_word[9:(DLY)]};
	end else
		always @(posedge i_clk)
			o_word <= w_use_this_word;
	endgenerate

endmodule
