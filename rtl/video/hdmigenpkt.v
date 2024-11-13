////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/hdmigenpkt.v
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
// Copyright (C) 2024, Gisselquist Technology, LLC
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
module	hdmigenpkt (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[7:0]	S_DATA,
		// Verilator lint_off UNUSED
		input	wire		S_LAST,
		// input wire		S_ABORT,
		// Verilator lint_on  UNUSED
		//
		output	reg		M_VALID,
		input	wire		M_READY,
		output	wire		M_HDR,
		output	wire	[7:0]	M_DATA,
		output	wire		M_LAST,
		//
		output	reg	[31:0]	o_debug
		// }}}
	);

	// Accept packet inputs -- must be 31 bytes each: 3 hdr octets, 28data
	// Local declarations
	// {{{
	localparam	IPKTLEN = 3+28,
			OPKTLEN = 32,
			LGFLEN  = 6;
	reg			fsm_header, fsm_data;
	reg	[5:0]		icount, ecount;
	reg	[1:0]		loaded;
	wire	[LGFLEN:0]	ign_fif_fill;
	wire			fif_full, fif_empty, fifo_reset;

	reg			ivalid;
	wire			iready;
	reg	[8:0]		idata;
	reg			ilast;
	reg	[7:0]		b0fill, b1fill, b2fill, b3fill, hdrfill;
	reg	[30:0]		hdrsreg;

	reg			abort;
	reg	[23:0]		hdrin;
	// }}}

	assign	S_READY = (fsm_header || fsm_data || abort)
			&& (icount != 3 || !ivalid || ilast)
					&& (!ivalid || iready);

	// icount, ecount
	// {{{
	initial	icount     = 0;
	initial	fsm_data   = 0;
	initial	fsm_header = 1;
	always @(posedge i_clk)
	if (i_reset || abort)
	begin
		icount     <= 0;
		fsm_data   <= 0;
		fsm_header <= 1;
	end else if (S_VALID && S_READY)
	begin
		icount <= icount + 1;
		if (S_LAST || icount >= IPKTLEN-1)
		begin
			icount <= 0;
			fsm_header <= 1;
			fsm_data   <= 0;
		end else begin
			fsm_header <= (icount <= 1);
			fsm_data   <= (icount >= 2);
		end
	end
`ifdef	FORMAL
	always @(*)
	begin
		assert(icount <= IPKTLEN-1);
		assert(fsm_header == (icount < 3));
		assert(fsm_header == !fsm_data);
	end
`endif

	initial	ecount = 0;
	always @(posedge i_clk)
	if (i_reset || abort)
		ecount <= 0;
	// else if (S_VALID && S_READY && fsm_data)
	//	ecount <= icount - 3;
	else if (ivalid && iready) // && ecount >= IPKTLEN-4)
	begin
		ecount <= ecount + 1;
		if (ilast)
			ecount <= 0;
	end
`ifdef	FORMAL
	always @(*)
	begin
		assert(ecount <= OPKTLEN-1);
		if (icount >= 4)
			assert(ecount + 4 == icount + (ivalid ? 0:1));
		if (!abort && icount <= 3 && (ivalid || ecount > 0))
			assert(ecount + (ivalid ? 1:0) >= OPKTLEN-4);
	end
`endif
	// }}}

	// Header processing: hdrin, hdrfill
	// {{{
	always @(posedge i_clk)
	if (i_reset || abort)
	begin
		hdrfill <= 8'h00;
		hdrin   <= 0;
	end else if (S_VALID && S_READY && fsm_header)
	begin
		if (icount == 0)
		begin
			hdrfill <= ECCBYTE(8'h0, S_DATA);
			hdrin[23:16] <= S_DATA;
		end else if (icount == 1)
		begin
			hdrfill <= ECCBYTE(hdrfill, S_DATA);
			hdrin[15:8] <= S_DATA;
		end else if (icount == 2)
		begin
			hdrfill <= ECCBYTE(hdrfill, S_DATA);
			hdrin[7: 0] <= S_DATA;
		end
	end else if (S_VALID && S_READY && fsm_data)
	begin
		hdrfill <= 0;
		hdrin <= 24'h0;
	end
	// }}}

	// hdrsreg, b?fill
	// {{{
	initial	ivalid = 0;
	always @(posedge i_clk)
	if (i_reset || ((!ivalid || !ilast || iready) && abort))
		ivalid <= 1'b0;
	else if (S_VALID && S_READY && fsm_data)
		ivalid <= 1'b1;
	else if (ivalid && iready)
	begin
		ivalid <= 0;
		if (ecount > IPKTLEN-5)
			ivalid <= (ecount <= OPKTLEN-2);
	end

	always @(posedge i_clk)
	if (S_VALID && S_READY && fsm_data)
	begin
		if (icount == 3)
		begin
			hdrsreg <= { hdrin[22:0], hdrfill };	// 23+8=31b reg
			idata <= { hdrin[23], S_DATA };

			b0fill <= ECCFN(ECCFN(8'h00, S_DATA[0]), S_DATA[4]);
			b1fill <= ECCFN(ECCFN(8'h00, S_DATA[1]), S_DATA[5]);
			b2fill <= ECCFN(ECCFN(8'h00, S_DATA[2]), S_DATA[6]);
			b3fill <= ECCFN(ECCFN(8'h00, S_DATA[3]), S_DATA[7]);
		end else begin
			hdrsreg <= { hdrsreg[29:0], 1'b0 };
			idata <= { hdrsreg[30], S_DATA };
			b0fill <= ECCFN(ECCFN(b0fill, S_DATA[0]), S_DATA[4]);
			b1fill <= ECCFN(ECCFN(b1fill, S_DATA[1]), S_DATA[5]);
			b2fill <= ECCFN(ECCFN(b2fill, S_DATA[2]), S_DATA[6]);
			b3fill <= ECCFN(ECCFN(b3fill, S_DATA[3]), S_DATA[7]);
		end
	end else if (iready && ecount >= IPKTLEN-5)
	begin
		hdrsreg <= { hdrsreg[29:0], 1'b0 };
		idata  <= { hdrsreg[30],
				b3fill[6], b2fill[6], b1fill[6], b0fill[6],
				b3fill[7], b2fill[7], b1fill[7], b0fill[7] };

		b0fill <= { b0fill[5:0], 2'b00 };
		b1fill <= { b1fill[5:0], 2'b00 };
		b2fill <= { b2fill[5:0], 2'b00 };
		b3fill <= { b3fill[5:0], 2'b00 };
	end
	// }}}

	// ilast
	// {{{
	initial	ilast = 0;
	always @(posedge i_clk)
	if (i_reset || (abort && (!ivalid || !ilast || iready)))
		ilast <= 0;
	else if (ivalid && iready)
		ilast <= (ecount == OPKTLEN-2);
`ifdef	FORMAL
	always @(*)
		assert(abort || ilast == (ecount == OPKTLEN-1));
	always @(*)
	if (ecount > OPKTLEN-5)
		assert(ivalid);
`endif
	// }}}

	// loaded
	// {{{
	initial	loaded = 0;
	always @(posedge i_clk)
	if (i_reset || (!ivalid && fif_empty))
		loaded <= 0;
	else case({(ivalid && iready && ilast),(M_VALID && M_READY && M_LAST) })
	2'b10: loaded <= loaded + 1;
	2'b01: loaded <= loaded - 1;
	default: begin end
	endcase
`ifdef	FORMAL
	always @(*)
		assert(loaded <= 2);
`endif
	// }}}

	// abort
	// {{{
	initial	abort = 0;
	always @(posedge i_clk)
	if (i_reset)
		abort <= 0;
	else if (abort && S_VALID && S_READY && S_LAST && loaded == 0)
		abort <= 0;
	else begin
		if (S_VALID && S_READY && S_LAST != (icount == IPKTLEN-1))
			abort <= 1'b1;
		if (fif_full && loaded == 0)
			abort <= 1'b1;
	end
	// }}}

`ifdef	FORMAL
	wire	[LGFLEN:0]	ffif_first_addr, ffif_second_addr,
			ffif_distance_to_first, ffif_distance_to_second;
	wire	[9:0]	ffif_first_data, ffif_second_data;
	wire		ffif_first_in_fifo, ffif_second_in_fifo;
	wire		ffif_first_return, ffif_second_return,
			ffif_assume_return;
`endif
	assign	fifo_reset = i_reset || (abort
			&& (!ivalid || !ilast) && (loaded == 0));
	sfifo #(
		.BW(10), .LGFLEN(LGFLEN)
	) u_fifo(
		// {{{
		.i_clk(i_clk), .i_reset(i_reset || fifo_reset),
		.i_wr(ivalid), .i_data({ ilast, idata }), .o_full(fif_full),
			.o_fill(ign_fif_fill),
		.i_rd(loaded != 0 && M_READY),
			.o_data({ M_LAST, M_HDR, M_DATA }),
			.o_empty(fif_empty)
`ifdef	FORMAL
		, .f_first_addr(ffif_first_addr),
		.f_second_addr(ffif_second_addr),
		.f_first_data(ffif_first_data),
		.f_second_data(ffif_second_data),
		.f_first_in_fifo(ffif_first_in_fifo),
		.f_second_in_fifo(ffif_second_in_fifo),
		.f_distance_to_first(ffif_distance_to_first),
		.f_distance_to_second(ffif_distance_to_second)
`endif
		// }}}
	);

	initial	M_VALID = 0;
	always @(posedge i_clk)
	if (i_reset)
		M_VALID <= 1'b0;
	else if (ivalid && iready && ilast)
		M_VALID <= 1'b1;
	else if (M_VALID && M_READY && M_LAST)
		M_VALID <= (loaded > 1);
`ifdef	FORMAL
	always @(*)
	if (!i_reset)
		assert(M_VALID == (!fif_empty && loaded != 0));
`endif
	assign	iready  = !fif_full;

	localparam	[7:0]	ECCPOLY= 8'hc1;

	function automatic [7:0] ECCFN(input [7:0] fill, input b);
		// {{{
	begin
		if (b ^ fill[7])
			ECCFN = { fill[6:0], 1'b0 } ^ ECCPOLY;
		else
			ECCFN = { fill[6:0], 1'b0 };
	end endfunction
	// }}}

	function automatic [7:0] ECCBYTE(input [7:0] fill, input [7:0] in);
		// {{{
		integer		ik;
		reg	[7:0]	lfill;
	begin
		lfill = fill;
		for(ik=0; ik<8; ik=ik+1)
			lfill = ECCFN(lfill, in[7-ik]);
		ECCBYTE = lfill;
	end endfunction
	// }}}

	always @(posedge i_clk)
	begin
		o_debug <= 32'h0;
		o_debug[3 +: LGFLEN+1] <= ign_fif_fill;
		o_debug[31] <= M_VALID && M_READY && M_LAST;
		o_debug[30:24] <= M_DATA[6:0];
		o_debug[23] <= S_VALID;
		o_debug[22] <= S_READY;
		o_debug[21] <= S_LAST;
		//
		o_debug[20] <= M_VALID;
		o_debug[19] <= M_READY;
		o_debug[18] <= M_HDR;
		o_debug[17] <= M_LAST;
		//
		o_debug[16] <= ivalid;
		o_debug[15:10] <= icount;
		o_debug[  9] <= ilast;
		o_debug[  2] <= (loaded != 0);
		o_debug[1:0] <= loaded[1:0];
	end

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, ign_fif_fill };
	// Verilator lint_on  UNUSED
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
	reg	[15:0]	fm_count, fm_posn;
	reg	[4:0]	fs_posn;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);
	////////////////////////////////////////////////////////////////////////
	//
	// Incoming stream properties
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assume(!S_VALID);
	end else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_LAST));
	end

	initial	fs_posn = 0;
	always @(posedge i_clk)
	if (i_reset)
		fs_posn <= 0;
	else if (S_VALID && S_READY)
	begin
		fs_posn <= fs_posn + 1;
		if (S_LAST)
			fs_posn <= 0;
	end

	always @(*)
	if (!i_reset && !abort)
	begin
		assert(fs_posn == icount);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Outgoing stream properties
	// {{{

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
	begin
		assert(!M_VALID);
	end else if ($past(M_VALID && !M_READY))
	begin
		assert(M_VALID);
		assert($stable(M_HDR));
		assert($stable(M_DATA));
		assert($stable(M_LAST));
	end

	initial	fm_posn = 0;
	always @(posedge i_clk)
	if (i_reset)
		fm_posn <= 0;
	else if (M_VALID && M_READY)
	begin
		fm_posn <= fm_posn + 1;
		if (M_LAST)
			fm_posn <= 0;
	end

	always @(*)
	if (M_VALID)
		assert(M_LAST == (&fm_posn[4:0]));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Internal properties
	// {{{
	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assert(!ivalid);
	else if ($past(ivalid && !iready) && !abort)
	begin
		assert(ivalid);
		assert($stable(ilast));
		assert($stable(idata));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// FIFO properties
	// {{{

	assign	ffif_first_return = ffif_first_in_fifo && (ffif_distance_to_first == 0);
	assign	ffif_second_return = ffif_second_in_fifo && (ffif_distance_to_second == 0);
	assign	ffif_assume_return = !fif_empty && !ffif_first_return && !ffif_second_return;

	always @(*)
	begin
		if (ffif_first_return && ffif_second_return)
			assert(!ffif_first_data[8] || !ffif_second_data[8]);
	end

	wire	[15:0]		ffif_first_posn, ffif_second_posn, ffif_eposn,
				ffif_last_posn, ffif_ilast_posn;
	reg	[4:0]		ffif_distance_to_eop;
	reg	[LGFLEN:0]	ffif_distance_to_last, ffif_distance_to_ilast;

	assign	ffif_first_posn = fm_posn + ffif_distance_to_first;
	assign	ffif_second_posn = fm_posn + ffif_distance_to_second;
	assign	ffif_eposn = fm_posn + ign_fif_fill - 1 + (ivalid ? 1:0);

	always @(*)
	begin
		ffif_distance_to_last = ign_fif_fill - 1;
		ffif_last_posn = fm_posn + ffif_distance_to_last;

		ffif_distance_to_ilast = ffif_distance_to_last+(OPKTLEN-ecount);
		ffif_ilast_posn = fm_posn + ffif_distance_to_ilast;

		ffif_distance_to_eop = (OPKTLEN-1) - fm_posn[4:0];
	end

	always @(*)
	begin
		// fif_fill
		if (ffif_first_in_fifo)
		begin
			assert(ffif_first_data[9] == (&ffif_first_posn[4:0]));
			if (ffif_distance_to_eop == ffif_distance_to_first)
			begin
				assert(ffif_first_data[9]);
				assert(loaded > 0);
			end // else if (ffif_distance_to_eop == ffif_distance_to_first)
			//	assert(loaded > 0);
		end

		if (ffif_second_in_fifo)
		begin
			assert(ffif_second_data[9] == (&ffif_second_posn[4:0]));
			if (ffif_distance_to_eop == ffif_distance_to_second)
			begin
				assert(ffif_second_data[9]);
				assert(loaded > 0);
			end // else if (ffif_distance_to_eop == ffif_distance_to_second)
			//	assert(loaded > 0);
		end

		if (!fif_empty)
		begin
			assert(abort || (ecount == 0) == (&ffif_last_posn[4:0]));
			assert(abort || (&ffif_ilast_posn[4:0]));
		end else begin
			assert(ecount == 0);
			assert(loaded == 0);
			assert(fm_posn[4:0] == 0);	// !!!
		end

		if (fm_posn[4:0] != 0)
			assert(!fif_empty && loaded != 0);
		if (!fif_empty && ffif_distance_to_eop < ign_fif_fill)
			assert(loaded > 0);
		if (ffif_distance_to_eop > ign_fif_fill)
			assert(loaded == 0);
		if (OPKTLEN + ffif_distance_to_eop > ign_fif_fill)
			assert(loaded <= 1);
		if (!fif_empty && OPKTLEN + ffif_distance_to_eop < ign_fif_fill)
			assert(loaded > 1);

		if (ign_fif_fill >= OPKTLEN)
			assert(loaded >= 1);
		if (ign_fif_fill < OPKTLEN)
			assert(loaded <= 1);

		if (ffif_assume_return)
			assume(M_LAST == (&fm_posn[4:0]));
		if (ffif_assume_return || abort)
			assume(M_LAST == (ign_fif_fill == 1));
		// if (!abort && ecount > 0)
		//	assert(ecount[4:0] == ffif_eposn[4:0]);
	end

	always @(*)
	if (loaded == 2)
		assert(!ivalid || !ilast || (&fm_posn[4:0]));

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover checks
	// {{{
	reg	[4:0]	cvr_packets, cvr_load;

	initial	cvr_packets = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_packets <= 0;
	else if (!cvr_packets[4] && M_VALID && M_READY && M_LAST)
		cvr_packets <= cvr_packets + 1;

	initial	cvr_load = 0;
	always @(posedge i_clk)
	if (i_reset)
		cvr_load <= 0;
	else if (!cvr_load[4] && ivalid && iready && ilast)
		cvr_load <= cvr_load + 1;

	always @(*)
	begin
		cover(cvr_load > 0);
		cover(cvr_load > 1);
		cover(cvr_load > 2);
		cover(cvr_packets > 0);
		cover(cvr_packets > 1);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{
	// always @(*) assume(loaded <= 2);
	always @(*)
	begin
		// assume(!abort);
		// if (ign_fif_fill >= OPKTLEN) assume(loaded >= 1);
		// if (ign_fif_fill < OPKTLEN) assume(loaded <= 1);
		// if (fif_empty) assume(loaded == 0);
	end
	// }}}
`endif
// }}}
endmodule
