////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	busexpander.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	The ZipCPU uses a 32-bit bus.  Memory uses a 128-bit bus.
//		This just accomplishes the translation between the two.
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
`default_nettype none
//
module	busexpander(i_clk, i_reset,
		i_s_cyc, i_s_stb, i_s_we, i_s_addr, i_s_data, i_s_sel,
			o_s_stall, o_s_ack, o_s_data, o_s_err,
		o_m_cyc, o_m_stb, o_m_we, o_m_addr, o_m_data, o_m_sel,
			i_m_stall, i_m_ack, i_m_data, i_m_err);
	parameter	AWIN=30, DWIN=32, DWOUT=128;
	parameter	AWOUT=
				(DWOUT == DWIN) ? AWIN
				: ((DWOUT/DWIN==2) ? AWIN-1
				: ((DWOUT/DWIN==4) ? AWIN-2
				: ((DWOUT/DWIN==8) ? AWIN-3
				: ((DWOUT/DWIN==16) ? AWIN-4
				: AWIN-5))));
	parameter	LGFIFO = 5;
	localparam	FIFO_WIDTH = AWIN - AWOUT;
	//
	input	wire			i_clk, i_reset;
	//
	// First wishbone port:
	//
	//	the port with the smaller size
	//
	input	wire			i_s_cyc, i_s_stb, i_s_we;
	input	wire	[(AWIN-1):0]	i_s_addr;
	input	wire	[(DWIN-1):0]	i_s_data;
	input	wire	[(DWIN/8-1):0]	i_s_sel;
	//
	output	reg			o_s_stall;
	output	reg			o_s_ack;
	output	reg	[(DWIN-1):0]	o_s_data;
	output	reg			o_s_err;
	//
	// First wishbone port:
	//
	//	the port with the smaller size
	//
	output	reg			o_m_cyc, o_m_stb, o_m_we;
	output	reg	[(AWOUT-1):0]	o_m_addr;
	output	reg	[(DWOUT-1):0]	o_m_data;
	output	reg	[(DWOUT/8-1):0]	o_m_sel;
	//
	input	wire			i_m_stall;
	input	wire			i_m_ack;
	input	wire	[(DWOUT-1):0]	i_m_data;
	input	wire			i_m_err;
	//

	// Delayed register set
	reg			r_stb, r_we;
	reg	[(AWOUT-1):0]	r_addr;
	reg	[(DWOUT-1):0]	r_data;
	reg	[(DWOUT/8-1):0]	r_sel;

	// A memory to help us select the proper output upon return
	reg	[LGFIFO:0]		wr_addr, rd_addr;
	reg	[(FIFO_WIDTH-1):0]	subaddr;
	reg	[(FIFO_WIDTH-1):0]	fifo	[0:((1<<LGFIFO)-1)];
	reg				fifo_almost_full;
	wire	[LGFIFO:0]		fifo_fill;


	//
	//
	// The output set
	//
	initial	o_m_cyc = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_m_cyc <= 1'b0;
	else if ((i_s_cyc && o_s_err)||(o_m_cyc && i_m_err))
		o_m_cyc <= 1'b0;
	else
		o_m_cyc <= (o_m_cyc && i_s_cyc) || i_s_stb;

	initial	r_stb = 0;
	initial	o_m_stb = 1'b0;
	always @(posedge i_clk)
	begin
		if ((!i_m_stall)||(!o_m_stb))
		begin
			if (r_stb)
			begin
				o_m_stb  <= i_s_cyc;
				o_m_we   <= r_we;
				o_m_addr <= r_addr;
				o_m_data <= r_data;
				o_m_sel  <= r_sel;
				//
			end else begin
				o_m_stb  <= i_s_stb && !o_s_stall;
				o_m_we   <= i_s_we;
				o_m_addr <= i_s_addr[(AWIN-1):(AWIN-AWOUT)];
				case(i_s_addr[(AWIN-AWOUT-1):0])
				2'b00:o_m_data <= {        i_s_data, 96'h00 };
				2'b01:o_m_data <= { 32'h0, i_s_data, 64'h00 };
				2'b10:o_m_data <= { 64'h0, i_s_data, 32'h00 };
				2'b11:o_m_data <= { 96'h0, i_s_data };
				endcase

				case(i_s_addr[(AWIN-AWOUT-1):0])
				2'b00:o_m_sel <= {        i_s_sel, 12'h00 };
				2'b01:o_m_sel <= {  4'h0, i_s_sel,  8'h00 };
				2'b10:o_m_sel <= {  8'h0, i_s_sel,  4'h00 };
				2'b11:o_m_sel <= { 12'h0, i_s_sel         };
				endcase
				//
			end
			r_stb    <= 1'b0;
		end else if (!r_stb)
			r_stb <= (i_s_stb && !o_s_stall);

		if (!r_stb)
		begin
			r_we  <= i_s_we;
			r_addr <= i_s_addr[(AWIN-1):(AWIN-AWOUT)];
			//
			case(i_s_addr[(AWIN-AWOUT-1):0])
			2'b00:	r_data <= {        i_s_data, 96'h00 };
			2'b01:	r_data <= { 32'h0, i_s_data, 64'h00 };
			2'b10:	r_data <= { 64'h0, i_s_data, 32'h00 };
			2'b11:	r_data <= { 96'h0, i_s_data };
			endcase

			case(i_s_addr[(AWIN-AWOUT-1):0])
			2'b00:	r_sel <= {        i_s_sel, 12'h00 };
			2'b01:	r_sel <= {  4'h0, i_s_sel,  8'h00 };
			2'b10:	r_sel <= {  8'h0, i_s_sel,  4'h00 };
			2'b11:	r_sel <= { 12'h0, i_s_sel         };
			endcase
		end

		if ((!i_s_cyc)||((i_m_err)&&(o_m_cyc))||(o_s_err))
		begin
			o_m_stb  <= 1'b0;
			r_stb    <= 1'b0;
		end

		if (i_reset)
		begin
			r_stb <= 0;
			o_m_stb <= 1'b0;
		end
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing / slave side stall
	//
	// Normally this would be as simple as o_s_stall == r_stb.  However,
	// we also need to double check that we never overrun our FIFO.
	//
	initial	o_s_stall = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc)
		o_s_stall <= 1'b0;
	else if (o_m_stb && i_m_stall && (r_stb || (i_s_stb && !o_s_stall)))
		o_s_stall <= 1'b1;
	else if (fifo_almost_full)
		o_s_stall <= 1'b1;
	else
		o_s_stall <= 1'b0;


	////////////////////////////////////////////////////////////////////////
	//
	// Sub-address FIFO
	//
	initial	wr_addr = 0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc)
		wr_addr <= 0;
	else if ((i_s_stb)&&(!o_s_stall))
		wr_addr <= wr_addr + 1'b1;

	always @(posedge i_clk)
	if (i_s_stb && !o_s_stall)
		fifo[wr_addr[LGFIFO-1:0]] <= i_s_addr[1:0];

	initial	rd_addr = 0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc)
		rd_addr <= 0;
	else if (o_m_cyc && i_m_ack)
		rd_addr <= rd_addr + 1'b1;

	always @(*)
		subaddr = fifo[rd_addr[LGFIFO-1:0]];

	assign	fifo_fill = wr_addr - rd_addr;

	initial	fifo_almost_full = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc)
		fifo_almost_full <= 1'b0;
	else case({ i_s_stb && !o_s_stall, i_m_ack })
	2'b01: fifo_almost_full <= fifo_fill[LGFIFO];
	2'b10: fifo_almost_full <= (fifo_fill >= { 1'b0, {(LGFIFO-1){1'b1}}, 1'b0} );
	default: begin end
	endcase

`ifdef	FORMAL
	always @(*)
	if (i_s_cyc)
		assert(fifo_almost_full == (fifo_fill >= { 1'b0, {(LGFIFO){1'b1}} }));
	always @(*)
	begin
		assert(fifo_fill <= { 1'b1, {(LGFIFO){1'b0}} });
		if (fifo_fill[LGFIFO])
			assert(o_s_stall);
	end
`endif
	////////////////////////////////////////////////////////////////////////
	//
	// Return acknowledgements
	//
	initial	o_s_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc || !o_m_cyc)
		o_s_ack <= 1'b0;
	else
		o_s_ack <= i_m_ack;

	initial	o_s_err = 0;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc || !o_m_cyc)
		o_s_err <= 1'b0;
	else
		o_s_err <= i_m_err;

	////////////////////////////////////////////////////////////////////////
	//
	//	Return data
	//
	always @(posedge i_clk)
	case(subaddr)
	2'b00: o_s_data <= i_m_data[127:96];
	2'b01: o_s_data <= i_m_data[ 95:64];
	2'b10: o_s_data <= i_m_data[ 63:32];
	2'b11: o_s_data <= i_m_data[ 31: 0];
	endcase

`ifdef	FORMAL
`ifdef	BUSXPANDER
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	localparam	F_LGDEPTH = LGFIFO+2, STALL_DELAY = 4, ACK_DELAY=8;

	reg	f_past_valid;
	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;


	wire	[(F_LGDEPTH-1):0]	f_m_nreqs, f_m_nacks, f_m_outstanding,
			f_s_nreqs, f_s_nacks, f_s_outstanding;

	fwb_slave #(.AW(AWIN), .DW(DWIN),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_STALL(0), // STALL_DELAY+2*ACK_DELAY+1),
		.F_MAX_ACK_DELAY(0), // ACK_DELAY+1+2*STALL_DELAY),
		.F_OPT_RMW_BUS_OPTION(1),
		.F_OPT_DISCONTINUOUS(1))
		f_wbs(i_clk, i_reset,
			i_s_cyc, i_s_stb, i_s_we, i_s_addr, i_s_data,
				i_s_sel,
			o_s_ack, o_s_stall, o_s_data, o_s_err,
			f_s_nreqs, f_s_nacks, f_s_outstanding);

	fwb_master #(.AW(AWOUT), .DW(DWOUT),
		.F_LGDEPTH(F_LGDEPTH),
		.F_MAX_STALL(STALL_DELAY),
		.F_MAX_ACK_DELAY(ACK_DELAY),
		.F_OPT_RMW_BUS_OPTION(1),
		.F_OPT_DISCONTINUOUS(1))
		f_wbm(i_clk, i_reset,
			o_m_cyc, o_m_stb, o_m_we, o_m_addr, o_m_data,
				o_m_sel,
			i_m_ack, i_m_stall, i_m_data, i_m_err,
			f_m_nreqs, f_m_nacks, f_m_outstanding);

	always @(*)
	if (i_s_cyc && o_m_cyc)
		assert(f_s_outstanding == f_m_outstanding + (r_stb ? 1:0) + (o_m_stb ? 1:0) + (o_s_ack ? 1:0));
	else if (i_s_cyc)
		assert(f_s_outstanding == 0 || o_s_err);

	always @(*)
	if (i_s_cyc)
		assert(f_s_outstanding == fifo_fill + (o_s_ack ? 1:0));

	always @(*)
		assert(f_s_nreqs[LGFIFO:0] == wr_addr);

	reg	[F_LGDEPTH-1:0]	f_m_nreqs_plus;

	always @(*)
		f_m_nreqs_plus <= f_m_nreqs + (o_m_stb ? 1:0) + (r_stb ? 1:0);

	always @(*)
	if (i_s_cyc && o_m_cyc)
		assert(f_m_nreqs_plus == f_s_nreqs);

	always @(posedge i_clk)
	if (f_past_valid && $past(!i_reset)
		&& $past(i_s_cyc && !o_s_err && (!o_m_cyc || !i_m_err)))
	begin
		if ($past(i_s_stb || (f_s_outstanding > 0)))
			assert(o_m_cyc);

		if (!o_m_cyc)
		begin
			assert(f_s_nacks == 0);
			assert(!o_s_ack);
		end
	end

//	wire	[2+AWIN+DWIN+DWIN/8-1:0]	f_spending, f_srequest;
//	wire	[2+AWOUT+DWOUT+DWOUT/8-1:0]	f_mrequest;
//	// assign	f_mpending = { r_stb, r_we, r_addr, r_data, r_sel };

//	assign	f_srequest = { i_s_stb, i_s_we, i_s_addr, i_s_data, i_s_sel };
//	assign	f_mrequest = { i_m_stb, i_m_we, i_m_addr, i_m_data, i_m_sel };

	////////////////////////////////////////////////////////////////////////
	//
	// FIFO checks
	//
	reg	[1:0]				f_fifo_state;
	(* anyconst *) reg	[LGFIFO:0]	f_first_addr;
	reg	[LGFIFO:0]			f_next_addr;
	reg	[(FIFO_WIDTH-1):0]		f_first_data, f_next_data;
	reg					f_infifo_first, f_infifo_next;
	reg	[LGFIFO:0]	f_first_distance, f_next_distance;


	always @(*)
		f_next_addr = f_first_addr + 1;

	always @(posedge i_clk)
	if (i_s_stb && !o_s_stall && (f_first_addr == wr_addr))
		f_first_data <= i_s_addr[FIFO_WIDTH-1:0];

	always @(posedge i_clk)
	if (i_s_stb && !o_s_stall && (f_next_addr == wr_addr))
		f_next_data <= i_s_addr[FIFO_WIDTH-1:0];

	always @(*)
	begin
		f_first_distance = f_first_addr - rd_addr;
		f_next_distance  = f_next_addr  - rd_addr;

		f_infifo_first = 1'b0;
		if (fifo_fill == 0)
			f_infifo_first = 0;
		else if (f_first_distance < fifo_fill)
			f_infifo_first = 1'b1;

		f_infifo_next = 1'b0;
		if (fifo_fill == 0)
			f_infifo_next = 0;
		else if (f_next_distance < fifo_fill)
			f_infifo_next = 1'b1;
	end

	initial	f_fifo_state = 2'b00;
	always @(posedge i_clk)
	if (i_reset || !i_s_cyc || i_m_err)
		f_fifo_state <= 2'b00;
	else case(f_fifo_state)
	2'b00: if (i_s_stb && !o_s_stall && (f_first_addr == wr_addr))
		f_fifo_state <= 2'b01;
	2'b01: if ((i_m_err | i_m_ack) && (rd_addr == f_first_addr))
			f_fifo_state <= 2'b00;
		else if (i_s_stb && !o_s_stall)
			f_fifo_state <= 2'b10;
	2'b10: if (i_m_ack && (f_first_addr == rd_addr))
		f_fifo_state <= 2'b11;
	2'b11: if (i_m_ack)
		f_fifo_state <= 2'b00;
	endcase

	always @(*)
	case(f_fifo_state)
	2'b00: begin end
	2'b01: begin
		assert(f_next_addr == wr_addr);
		assert(fifo[f_first_addr[LGFIFO-1:0]] == f_first_data);
		assert(fifo_fill >= 1);
		assert(f_infifo_first);
		end
	2'b10: begin
		assert(fifo[f_first_addr[LGFIFO-1:0]] == f_first_data);
		assert(fifo[f_next_addr[LGFIFO-1:0]]  == f_next_data);
		assert(fifo_fill >= 2);
		assert(f_infifo_first);
		assert(f_infifo_next);
		end
	2'b11: begin
		assert(f_next_addr == rd_addr);
		assert(fifo[f_next_addr[LGFIFO-1:0]]  == f_next_data);
		assert(fifo_fill >= 1);
		assert(f_infifo_next);
		end
	endcase
`endif
endmodule

