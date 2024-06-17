////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/sdspi/sdrxframe.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Process incoming data from the front end.  Data will come in
//		on (potentially) every edge of DS.  We need to turn it here
//	into one data stream for each IO pin, check the CRC on each data
//	stream, and then compose the results into (up to) 32-bits per clock
//	cycle to be written to the SRAM on an outgoing stream.
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
module	sdrxframe #(
		// {{{
		parameter	LGLEN = 15, NUMIO=4,
		parameter	MW = 32,
		localparam	LGLENW = LGLEN-$clog2(MW/8),
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		parameter [0:0]	OPT_DS = 1'b0,
		parameter [0:0]	OPT_LOWPOWER = 1'b0,
		parameter	LGTIMEOUT = 23	// 8 of slowest clock cycle
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_cfg_ds, i_cfg_ddr,
		input	wire	[1:0]		i_cfg_width,
		//
		input	wire			i_rx_en,
		input	wire			i_crc_en,
		input	wire	[LGLEN:0]	i_length,	// In bytes
		//
		input	wire	[1:0]		i_rx_strb,
		input	wire	[15:0]		i_rx_data,

		input	wire			S_ASYNC_VALID,
		input	wire	[31:0]		S_ASYNC_DATA,

		output	wire			o_mem_valid,
		output	wire	[MW/8-1:0]	o_mem_strb,
		output	wire	[LGLENW-1:0]	o_mem_addr,	// Word address
		output	wire	[MW-1:0]	o_mem_data,	// Outgoing data

		output	reg			o_active,
		output	reg			o_done,
		output	reg			o_err,
		output	reg			o_ercode
		// }}}
	);

	// Local declarations
	// {{{
	localparam	[1:0]	WIDTH_1W = 2'b00,
				WIDTH_4W = 2'b01,
				// Verilator lint_off UNUSED
				WIDTH_8W = 2'b10;
				// Verilator lint_on  UNUSED

	localparam	NCRC = 16;
	localparam	[NCRC-1:0]	CRC_POLYNOMIAL = 16'h1021;
	genvar	gk;

	reg	[4:0]	sync_fill;
	reg	[19:0]	sync_sreg;

	reg		s2_valid;
	reg	[1:0]	s2_fill;
	reg	[15:0]	s2_data;

	reg				mem_valid, mem_full, rnxt_strb;
	reg	[MW/8-1:0]		mem_strb;
	reg	[MW-1:0]		mem_data;
	reg	[LGLENW-1:0]		mem_addr;
	reg	[$clog2(MW/8)-1:0]	subaddr, next_subaddr;
	reg	[7:0]			rnxt_data;

	reg			busy, data_phase, load_crc, pending_crc;
	reg	[LGLEN+4-1:0]	rail_count;

	wire	[NUMIO*2-1:0]	err;

	reg	[LGTIMEOUT-1:0]	r_timeout;
	reg			r_watchdog;

	reg	last_strb;
	reg	w_done;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Notes:
	// {{{
	// Two channels of processing:
	//	 Sync processing: (No data strobe)
	//	0. The PHY will sample data a fixed distance from each clk edge
	//		That means it will always be sampling, whether or not
	//		we're expecting something.
	//	1. Wait for the enable
	//	2. Wait for the start bit: (S_VALID && S_DATA != 8'hff)
	//	3. Capture every S_VALID, and realign incoming bits
	//	4. Move to stage #2
	//
	//	Async processing: (w/ data strobe)
	//	0. The PHY will detect DS edges for us, and provide data
	//		VALID, (READY *MUST* be true), DATA, STRB
	//	1. Pack data into M_VALID, 32bits of M_DATA, M_LAST
	//	2. Move to stage #2
	//
	// Stage #2
	//	1. Calculate CRC on each of the 8 channels
	//	2. Generate error on failed CRC, failed start, or failed stop
	//	3. Drop unused data paths
	//
	// Potential errors:
	//	Start bits not aligned
	//	Stop bits not aligned, or not at the right place
	//	Failed CRC on a data bit we are using
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Synchronous (no DS) data path
	// {{{

	// Step #1: Bit sync
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS) || !data_phase)
		sync_fill <= 0;
	else if (i_rx_strb == 0)
	begin
		sync_fill[4:3] <= 2'b0;
	// Verilator lint_off WIDTH
	end else case(i_cfg_width)
	WIDTH_1W: sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 1:0)
						+ (i_rx_strb[0] ? 1:0);
	WIDTH_4W: sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 4:0)
						+ (i_rx_strb[0] ? 4:0);
	default:  sync_fill <= sync_fill[2:0] + (i_rx_strb[1] ? 8:0)
						+ (i_rx_strb[0] ? 8:0);
	endcase
	// Verilator lint_on  WIDTH

	always @(posedge i_clk)
	if (!i_rx_en)
		sync_sreg <= 0;
	else if (i_rx_strb != 0)
	begin
		case(i_cfg_width)
		WIDTH_1W: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[17:0], i_rx_data[8], i_rx_data[0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[18:0], i_rx_data[8] };
			else
				sync_sreg <= { sync_sreg[18:0], i_rx_data[0] };
		WIDTH_4W: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[11:0], i_rx_data[11:8], i_rx_data[3:0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[15:0], i_rx_data[11:8] };
			else
				sync_sreg <= { sync_sreg[15:0], i_rx_data[3:0] };
		default: if (i_rx_strb == 2'b11)
			sync_sreg <= { sync_sreg[3:0], i_rx_data[15:8], i_rx_data[7:0] };
			else if (i_rx_strb[1])
				sync_sreg <= { sync_sreg[11:0], i_rx_data[15:8] };
			else
				sync_sreg <= { sync_sreg[11:0], i_rx_data[7:0] };
		endcase
	end
	// }}}

	// Step #2: Byte sync: s2_valid, s2_fill (byte count), and s2_data
	// {{{
	// We assume this register gets fully and completely emptied on every
	// cycle, so we only have to capture what spills out from the sync_*
	// registers.
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS))
		// If RX is not enabled, or
		//   or we haven't seen the sync bit(s)
		//   or we are using the async path,
		// Then keep s2 disabled
		s2_valid <= 0;
	else
		s2_valid <= (sync_fill >= 8);

	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (i_cfg_ds && OPT_DS))
		s2_fill <= 0;
	else
		s2_fill <= sync_fill[4:3];

	// Verilator lint_off WIDTH
	always @(posedge i_clk)
	if (OPT_LOWPOWER && (!i_rx_en || (i_cfg_ds && OPT_DS)))
		s2_data <= 0;
	else if (sync_fill[4])
		s2_data <= sync_sreg >> sync_fill[2:0];
	else if (sync_fill[3])
		s2_data <= {sync_sreg, 8'h0} >> sync_fill[2:0];
	// Verilator lint_on  WIDTH
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Asynchronous (w/ DS) data path
	// {{{

	// Nothing really more needs to be done.  The async path comes in at
	// 4bytes at a times, all four valid (presently), and needs to be
	// synchronized to a 4-byte stream w/ all four valid.  Of course, this
	// will only work as long as the DS strobe signals only ever arrive
	// in pairs of pulses.

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Align, and write to (external) memory
	// {{{
	// (Memory is just external to this module, not necessarily to the chip)
	////////////////////////////////////////////////////////////////////////
	//
	//

	// o_mem_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full || r_watchdog
			|| (mem_valid && (&mem_addr) && mem_strb[0]))
		mem_valid <= 0;
	else if (!i_cfg_ds || !OPT_DS)
	begin
		mem_valid <= s2_valid || rnxt_strb;
	end else begin
		mem_valid <= S_ASYNC_VALID && data_phase;
	end

	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
		mem_full <= 0;
	else if (mem_valid && (&mem_addr) && mem_strb[0])
		mem_full <= 1;

	assign	o_mem_valid = mem_valid;
	// }}}

	// o_mem_addr
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full
			|| (mem_valid && (&mem_addr) && mem_strb[0]))
		next_subaddr <= 0;
	else if (!i_cfg_ds || !OPT_DS)
		next_subaddr <= next_subaddr + s2_fill;
	// else if (S_ASYNC_VALID)
	//	next_subaddr <= next_subaddr + 4;
	else
		next_subaddr <= subaddr;

	always @(posedge i_clk)
	if (i_reset || !i_rx_en)
		{ mem_addr, subaddr } <= 0;
	else if (o_mem_valid)
	begin
		// Verilator lint_off WIDTH
		{ mem_addr, subaddr } <= { mem_addr, subaddr } + COUNTONES(o_mem_strb);
		// Verilator lint_on  WIDTH
	end

	assign	o_mem_addr  = mem_addr;
	// }}}

	// o_mem_data, o_mem_strb
	// {{{
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || mem_full)
	begin
		mem_data <= 0;
		mem_strb <= 0;
		rnxt_data <= 0;
		rnxt_strb <= 0;
	end else if (!i_cfg_ds || !OPT_DS)
	begin

		if (s2_fill[1])
		begin
			{ mem_data, rnxt_data } <= { rnxt_data, {(MW){1'b0}} }
				|({ s2_data[15:0], {(MW-8){1'b0}} } >> (next_subaddr*8));
			{ mem_strb, rnxt_strb } <= { rnxt_strb, {(MW/8){1'b0}} }
				|({ 2'b11, {(MW/8-1){1'b0}} } >> (next_subaddr));
		end else if (s2_fill[0])
		begin
			{ mem_data, rnxt_data } <= {rnxt_data, {(MW){1'b0}} }
				|({ s2_data[15:8], {(MW){1'b0}} } >> (next_subaddr*8));
			{ mem_strb, rnxt_strb } <= { rnxt_strb, {(MW/8){1'b0}} }
				|({ s2_fill[0],{(MW/8){1'b0}} }>> next_subaddr);
		end else begin
			{ mem_data, rnxt_data } <= {rnxt_data,{(MW  ){1'b0}} };
			{ mem_strb, rnxt_strb } <= {rnxt_strb,{(MW/8){1'b0}} };
		end
	end else begin
		rnxt_data <= 0;
		rnxt_strb <= 0;
		mem_strb <= 0;

		if (S_ASYNC_VALID)
		begin
			mem_data <= { S_ASYNC_DATA, {(MW-32){1'b0}} } >> (next_subaddr*8);
			mem_strb <= { 4'hf, {(MW/8-4){1'b0}} } >> (next_subaddr);
		end
	end

	generate if (OPT_LITTLE_ENDIAN)
	begin : GEN_LIL_ENDIAN_SWAP
		reg	[MW/8-1:0]	swap_strb;
		reg	[MW-1:0]	swap_data;
		integer			ik;

		always @(*)
		for(ik=0; ik<MW/8; ik=ik+1)
		begin
			swap_strb[ik] = mem_strb[MW/8-1-ik];
			swap_data[ik*8 +: 8] = mem_strb[MW-ik*8 +: 8];
		end

		assign	o_mem_strb  = swap_strb;
		assign	o_mem_data  = swap_data;
	end else begin : NO_ENDIAN_SWAP
		assign	o_mem_strb  = mem_strb;
		assign	o_mem_data  = mem_data;
	end endgenerate
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Are we done?  Have we received a full packet?
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	always @(posedge i_clk)
	if (i_reset || o_done || !i_rx_en)
	begin
		rail_count <= 0;
		load_crc   <= 0;
		data_phase <= 0;
		last_strb  <= 0;
	end else if (!busy && i_rx_en)
	begin
		// {{{
		// Verilator lint_off WIDTH
		last_strb  <= (!i_crc_en && i_cfg_width == WIDTH_8W && i_length == 1);
		if (i_cfg_ds)
			rail_count <= i_length + (i_crc_en ? (16 + (i_cfg_ddr ? 16 : 0)) : 0);
		else case(i_cfg_width)
		WIDTH_1W: rail_count <= (i_length << 3) + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		WIDTH_4W: rail_count <= (i_length << 1) + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		default:  rail_count <= i_length + (i_crc_en ? (16 + (i_cfg_ddr ? 16:0)):0);
		endcase
		// Verilator lint_on  WIDTH

		data_phase <= 1;
		load_crc   <= 0;
		// }}}
	end else if (!i_cfg_ds || !OPT_DS)
	begin
		if (i_rx_strb == 2'b11)
		begin
			// {{{
			rail_count <= rail_count - 2;
			last_strb  <= (rail_count == 3);
			if (!i_crc_en)
			begin
				data_phase <= (rail_count > 2);
				load_crc   <= 1'b0;
			end else if (i_cfg_ddr)
			begin
				data_phase <= (rail_count > 16*2+2);
				load_crc   <= (rail_count <= 16*2+2)&&(rail_count > 2) && i_crc_en;
			end else begin
				data_phase <= (rail_count > 18);
				load_crc   <= (rail_count <= 18)&&(rail_count > 2) && i_crc_en;
			end

			if (rail_count < 2)
				rail_count <= 0;
			// }}}
		end else if (i_rx_strb[1])
		begin
			// {{{
			rail_count <= rail_count - 1;
			last_strb  <= (rail_count == 2);

			if (!i_crc_en)
			begin
				data_phase <= (rail_count > 1);
				load_crc   <= 1'b0;
			end else if (i_cfg_ddr)
			begin
				data_phase <= (rail_count >  16*2+1);
				load_crc   <= (rail_count <= 16*2+1)&&(rail_count > 1);
			end else begin
				data_phase <= (rail_count >  17);
				load_crc   <= (rail_count <= 17)&&(rail_count > 1);
			end

			if (rail_count < 1)
				rail_count <= 0;
			// }}}
		end
	end else if (S_ASYNC_VALID)
	begin
		// {{{
		rail_count <= rail_count - 4;
		last_strb  <= 0;

		if (!i_crc_en)
		begin
			data_phase <= (rail_count > 4);
			load_crc   <= 1'b0;
		end else if (i_cfg_ddr)
		begin
			data_phase <= (rail_count >  32+4);
			load_crc   <= (rail_count <= 32+4)&&(rail_count > 4);
		end else begin
			data_phase <= (rail_count >  16+4);
			load_crc   <= (rail_count <= 16+4)&&(rail_count > 4);
		end

		if ((rail_count < 4)||(i_cfg_ddr && rail_count < 8))
			rail_count <= 0;
		// }}}
	end

	always @(posedge i_clk)
	if (i_reset || o_done || !i_rx_en || !i_crc_en)
	begin
		pending_crc <= 1'b0;
	end else if ((i_rx_en && !busy) || load_crc || data_phase)
		pending_crc <= 1'b1;
	else if (!load_crc)
		pending_crc <= 1'b0;

	always @(*)
	begin
		w_done = !(data_phase || pending_crc || s2_valid
				|| sync_fill[4:3] != 2'b00 || mem_valid);
		if (r_watchdog)
			w_done = 1'b1;
		if (!busy)
			w_done = 1'b0;
	end

	always @(posedge i_clk)
	if (i_reset)
		busy <= 0;
	else if (!busy)
		busy <= i_rx_en && i_length > 0 && !o_done;
	else if (w_done)
		busy <= 1'b0;

	always @(posedge i_clk)
	if (i_reset)
		o_active <= 1'b0;
	else if (!busy)
		o_active <= i_rx_en && i_length > 0 && !o_done;
	else if (!i_cfg_ds || !OPT_DS)
		o_active <= (rail_count > (i_rx_strb[0] ? 1:0) + (i_rx_strb[1] ? 1:0));
	else
		o_active <= (rail_count > (S_ASYNC_VALID ? 4:0));
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// CRC checking
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	generate for(gk=0; gk<NUMIO; gk=gk+1)
	begin : GEN_RAIL_CRC
		reg	[15:0]		pedge_crc,
					nedge_crc;
		reg	[1:0]		lcl_err;

		// pedge_crc: POSEDGE Calculate the CRC for each rail
		// {{{
		initial	pedge_crc = 0;
		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en ||(!data_phase&&!load_crc))
			pedge_crc <= 0;
		else if ((gk >= 1 && i_cfg_width == WIDTH_1W)
				|| (gk >= 4 && i_cfg_width == WIDTH_4W))
			pedge_crc <= 0;
		else if (!i_cfg_ds || !OPT_DS)
		begin // CRC based upon synchronous inputs
			// {{{
			if (i_rx_strb == 2'b11 && !i_cfg_ddr && !last_strb)
				pedge_crc <= STEPCRC(STEPCRC(pedge_crc,
					i_rx_data[8+gk]),
					i_rx_data[  gk]);
			else if (i_rx_strb[1] && (!i_cfg_ddr || !rail_count[0]))
				pedge_crc <= STEPCRC(pedge_crc,i_rx_data[8+gk]);
			else if (i_rx_strb[0] &&  rail_count[0] && i_cfg_ddr)
				pedge_crc <= STEPCRC(pedge_crc,i_rx_data[0+gk]);
			// }}}
		end else if (S_ASYNC_VALID)
		begin // Asynchronous CRC generation
			// {{{
			// Note that in ASYNC mode, all rails are used
			if (i_cfg_ddr)
			begin
				pedge_crc <= STEPCRC( STEPCRC(pedge_crc,
					S_ASYNC_DATA[gk+24]),
					S_ASYNC_DATA[gk+ 8]);
			end else begin
				pedge_crc <= STEPCRC( STEPCRC(
					STEPCRC( STEPCRC(pedge_crc,
						S_ASYNC_DATA[gk+24]),
						S_ASYNC_DATA[gk+16]),
						S_ASYNC_DATA[gk+ 8]),
						S_ASYNC_DATA[gk   ]);
			end
			// }}}
		end
		// }}}

		// nedge_crc: NEGEDGE Calculate the CRC for each rail
		// {{{
		initial	nedge_crc = 0;
		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en || (!data_phase&&!load_crc)
								|| !i_cfg_ddr)
			nedge_crc <= 0;
		else if ((gk >= 1 && i_cfg_width == WIDTH_1W)
				|| (gk >= 4 && i_cfg_width == WIDTH_4W))
			// Zero out any unused rails
			nedge_crc <= 0;
		else if (!i_cfg_ds || !OPT_DS)
		begin // CRC based upon synchronous inputs
			// {{{
			if (i_rx_strb[1] && rail_count[0])
				nedge_crc <= STEPCRC(nedge_crc, i_rx_data[8+gk]);
			else if (i_rx_strb[0] && !rail_count[0])
				nedge_crc <= STEPCRC(nedge_crc, i_rx_data[0+gk]);
			// }}}
		end else if (S_ASYNC_VALID)
		begin // Asynchronous CRC generation
			// {{{
			// Note that in ASYNC mode, all rails are used (IIRC)
			nedge_crc <= STEPCRC( STEPCRC(nedge_crc,
						S_ASYNC_DATA[gk+16]),
						S_ASYNC_DATA[gk   ]);
			// }}}
		end
		// }}}

		always @(posedge i_clk)
		if (i_reset || !i_rx_en || !i_crc_en || data_phase || load_crc)
		begin
			lcl_err <= 2'b00;
		end else begin
			lcl_err[0] <= (pedge_crc != 0);

			lcl_err[1] <= (nedge_crc != 0) && i_cfg_ddr;
		end

		assign	err[gk] = lcl_err[0];
		assign	err[gk+NUMIO] = lcl_err[1];
	end endgenerate

	initial	o_done = 0;
	always @(posedge i_clk)
	if (i_reset || !i_rx_en || o_done || !busy)
		{ o_ercode, o_done, o_err } <= 0;
	else if (w_done)
	begin
		o_done <= 1'b1;
		o_err  <= (|err) || r_watchdog;
		o_ercode <= !r_watchdog;
	end

	function automatic [NCRC-1:0]	STEPCRC(input [NCRC-1:0] prior,
						input i_crc_data);
	begin
		if (prior[NCRC-1] ^ i_crc_data)
			STEPCRC = { prior[NCRC-2:0], 1'b0 } ^ CRC_POLYNOMIAL;
		else
			STEPCRC = { prior[NCRC-2:0], 1'b0 };
	end endfunction

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Watchdog timeout
	// {{{

	always @(posedge i_clk)
	if (i_reset || !i_rx_en || (!r_watchdog &&
			(((!OPT_DS || !i_cfg_ds) && i_rx_strb != 0)
			|| (OPT_DS && i_cfg_ds && S_ASYNC_VALID))))
	begin
		r_watchdog <= 0;
		r_timeout  <= -1;
	end else if (r_timeout != 0)
	begin
		r_watchdog <= (r_timeout <= 1);
		r_timeout  <= r_timeout - 1;
	end
	// }}}

	function automatic [$clog2(MW/8):0] COUNTONES(input [MW/8-1:0] set);
		integer ik;
	begin
		COUNTONES=0;
		for(ik=0; ik<MW/8; ik=ik+1)
		if (set[ik])
			COUNTONES=COUNTONES+1;
	end endfunction

	//
	// Make verilator happy
	// {{{
	// verilator coverage_off
	// verilator lint_off UNUSED
	// wire	unused;
	// assign	unused = i_wb_cyc;
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
