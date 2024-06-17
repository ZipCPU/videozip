////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/pkt2stream.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Converts an (abortable) packet stream to an AXI stream that
//		cannot be aborted while preserving packet length.
//	Output packets will start with a message length word containing the
//	length of the message in byte (excluding the message length word).
//	That many words (plus one) later you'll get to the next message length
//	word.
//
//	i_soft_reset	Resets the reader side independent of the network packet
//		generator.  Following a soft reset, we need to wait for
//		the LAST signal to resync before starting again.
//
// Format:
//	The stream that results will consist of ...
//		1. First word indicating the number of bytes in the packet.
//			THIS INCLUDES 4 BYTES FOR THIS FIRST WORD.
//		2. Many packed words containing packet data
//			Packet data will be kept in AXI order, where the
//			bits [7:0] are byte zero unless OPT_SWAPBYTES is true.
//
// Issues:
//	- Packets that don't fit into an otherwise empty FIFO will be aborted
//		and so dropped.
//	- Packets that don't fit into a partially filled FIFO will be stalled.
//		They may need to be dropped at the source if they cannot stall
//		long enough for this FIFO to have room.
//	- This behavior is not formally verified.  (A deadlock existed before,
//		the design was updated, and the same proof still passes.)
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
`default_nettype none
// }}}
module	pkt2stream #(
		// {{{
		parameter	BW=8,	// Incoming data width (one byte)
`ifdef	FORMAL
		parameter	MAX_PACKET_SIZE_BYTES=32,	// Size in bytes
`else
		parameter	MAX_PACKET_SIZE_BYTES=2048,	// Size in bytes
`endif
		// Downstream data (i.e. memory) width
		// {{{
		parameter	M_AXIS_DATA_WIDTH = 32,
		localparam	M_DW = M_AXIS_DATA_WIDTH,
		localparam	AXISLSB = $clog2(M_AXIS_DATA_WIDTH)-3,
		// }}}
		parameter [0:0]	OPT_LITTLE_ENDIAN = 1'b0,
		// FIFO size
		// {{{
		// 1. User chosen FIFO size
		parameter 	OPT_LGFLEN=$clog2(MAX_PACKET_SIZE_BYTES/(M_AXIS_DATA_WIDTH/8)),
		// 2. But the minimum FIFO size is two packets long
		localparam  MIN_LGFLEN=$clog2(MAX_PACKET_SIZE_BYTES)-AXISLSB,
		// 3. So let's pick a log_2 FIFO size from the max of the two.
		localparam	LGFLEN = (OPT_LGFLEN < MIN_LGFLEN)
						? MIN_LGFLEN : OPT_LGFLEN,
		localparam	FLEN=(1<<LGFLEN),
		// }}}
		//
		parameter [0:0]	OPT_ASYNC_READ = (LGFLEN < 8)
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		// i_soft_reset reset's the FIFO, but not necessarily the
		// source generator.  Everything downstream gets reset.
		// Any incoming packet needs to be aborted.
		input	wire		i_soft_reset,
		//
		// Incoming packets
		input	wire		S_AXIN_VALID,
		output	reg		S_AXIN_READY,
		input	wire [(BW-1):0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		//
		// Outgoing AXI stream
		output	wire		M_AXI_TVALID,
		input	wire		M_AXI_TREADY,
		output	wire [M_DW-1:0]	M_AXI_TDATA
		// No LAST in the outgoing interface (???)
		// No abort in the outgoing interface
		// }}}
	);

	// Register/net declarations
	// {{{
	localparam [1:0]	FSM_DATA = 2'b00, FSM_LAST = 2'b01,
				FSM_ADDR = 2'b10;
	reg			r_empty, packd_eop, packd_valid,
				pre_aborting, advance_mem;
	reg	[M_DW-1:0]	mem	[0:(FLEN-1)];
	reg	[M_DW-1:0]	packd_data, mem_data, next_packd_data;
	reg	[LGFLEN:0]	rd_addr, packd_eop_addr, tmp_eop_addr,
				packd_addr, next_packd_addr, wr_fill;
	wire			r_full;
	wire	[LGFLEN:0]	next_rd_addr;
	reg	[LGFLEN:0]	packd_words;
	reg	[LGFLEN-1:0]	mem_addr;
	reg	[M_DW-1:0]	packd_len, pre_bytes, tmp_len;
	reg	[1:0]		wr_state;
	wire			fifo_wr, fifo_data_wr, fifo_stall;
	reg			mem_wr;

	wire		w_wr, w_rd, s_abort;


	assign		w_wr = (S_AXIN_VALID && S_AXIN_READY && !S_AXIN_ABORT)
				&& !pre_aborting;
	assign		s_abort = S_AXIN_ABORT && (pre_bytes > 0)
				&& (!packd_valid || !packd_eop);
	assign		w_rd = (M_AXI_TVALID && M_AXI_TREADY);
	integer		ik;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step one: pack the data
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// Incoming:
	//	S_AXIN_VALID, w_wr, S_AXIN_DATA, S_AXIN_LAST, S_AXIN_ABORT
	//
	// Temporaries:
	//	pre_bytes, pre_aborting
	//
	// Interface
	//	packd_valid (TVALID), packd_data (TDATA), packd_eop (TLAST)
	//		(packd_len = length of TDATA)
	//	fifo_data_wr (TVALID && TREADY)
	//

	// S_AXIN_READY
	// {{{
	always @(*)
	if (S_AXIN_ABORT || pre_aborting)
		S_AXIN_READY = 1'b1;
	else if (fifo_stall)
		S_AXIN_READY = 1'b0;
	else
		S_AXIN_READY = !r_full;
	// }}}

	// pre_aborting
	// {{{
	// True if we need to wait for S_AXIN_VALID && S_AXIN_LAST before
	// accepting new packet data.  We do this:
	//
	// 1. In case the user hits i_soft_reset, but the source isn't
	// 	reset.  In that case, we might have to abandon an in progress
	//	packet--but the in progress packet isn't necessarily going to
	//	stop.  pre_aborting, therefore, is our indication of needing
	//	to abandon the current packet.
	//
	// 2. If the packet coming in would bust our buffer, we must also abort.
	//	Not all sources will raise ABORT.  Some synthetic sources may
	//	be able to wait forever.  Aborting here on a packet that's too
	//	large for our buffer, therefore, prevents deadlock on the
	//	channel.
	//
	initial	pre_aborting = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pre_aborting <= 0;
	else if (S_AXIN_ABORT)
		pre_aborting <= 0;
	else if (i_soft_reset && (packd_addr != packd_eop_addr + 1))
		pre_aborting <= (!S_AXIN_LAST || !w_wr);
	else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		if (S_AXIN_LAST)
			pre_aborting <= 0;
/*
		else if (wr_fill >= FLEN)
		begin
			pre_aborting <= 1;
`ifdef	FORMAL
			// I don't think we'll ever get here ...
			assert(0);
`endif
		end
*/
	end else if (S_AXIN_VALID && packd_words[LGFLEN])
		pre_aborting <= 1'b1;
	// }}}

	// pre_bytes
	// {{{
	initial	pre_bytes = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pre_bytes <= 0;
	else if (S_AXIN_ABORT || i_soft_reset)
		pre_bytes <= 0;
	else if (w_wr)
	begin
		if (S_AXIN_LAST)
			pre_bytes <= 0;
		else
			pre_bytes <= pre_bytes + 1;
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && pre_aborting)
		assert(pre_bytes == 0);
`endif
	// }}}

	// packd_words
	always @(*)
	begin
		// Verilator lint_off WIDTH
		packd_words = pre_bytes +  2 * M_DW / BW - 1;
		// Verilator lint_on  WIDTH
		packd_words = packd_words >> $clog2(M_DW / BW);
	end

	// packd_valid
	// {{{
	initial	packd_valid = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		packd_valid <= 0;
	else if (i_soft_reset || pre_aborting)
		packd_valid <= 0;
	else if (S_AXIN_ABORT && (!packd_valid || !packd_eop))
		packd_valid <= 0;
	else if (w_wr)
	begin
		if (S_AXIN_LAST)
			packd_valid <= 1;
		else
			packd_valid <= &pre_bytes[AXISLSB-1:0];
	end else if (fifo_data_wr)
		packd_valid <= 0;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && pre_aborting)
		assert(!packd_valid);

	always @(*)
	if (S_AXI_ARESETN && !packd_eop)
	begin
		if (pre_bytes[AXISLSB-1:0] != 0)
			assert(!packd_valid);
	end
`endif
	// }}}

	// packd_eop : does packd_data reference the last in the packet?
	// {{{
	initial	packd_eop = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		packd_eop <= 0;
	else if (i_soft_reset || pre_aborting)
		packd_eop <= 0;
	else if (S_AXIN_ABORT && (!packd_valid || !packd_eop))
		packd_eop <= 0;
	else begin
		if (fifo_data_wr)
			packd_eop <= 1'b0;
		if (w_wr)
			packd_eop <= S_AXIN_LAST;
	end
`ifdef	FORMAL
	always @(*)
	if (!packd_valid)
		assert(!packd_eop);
`endif
	// }}}

	// packd_data
	// {{{
	always @(*)
	begin
		if (packd_valid && fifo_data_wr)
			next_packd_data = 0;
		else
			next_packd_data = packd_data;

		if (w_wr)
		begin
			if (OPT_LITTLE_ENDIAN)
			begin
				next_packd_data = next_packd_data
					| ({ {(M_DW-BW){1'b0}}, S_AXIN_DATA }
					 	<< (pre_bytes[AXISLSB-1:0]*8));
			end else begin
				next_packd_data = next_packd_data
					| ({ S_AXIN_DATA, {(M_DW-BW){1'b0}} }
					 	>> (pre_bytes[AXISLSB-1:0]*8));
			end
		end
	end

	initial	packd_data = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		packd_data <= 0;
	else if (i_soft_reset || s_abort)
		packd_data <= 0;
	else
		packd_data <= next_packd_data;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && !packd_valid && (pre_bytes[AXISLSB-1:0] == 0))
		assert(packd_data == 0);
	always @(*)
	if (S_AXI_ARESETN && packd_eop)
		assert(packd_valid);
`endif
	// }}}

	// packd_len
	// {{{
	initial	packd_len = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		packd_len <= 0;
	else if (s_abort || i_soft_reset || pre_aborting)
		packd_len <= 0;
	else if (w_wr)
		packd_len <= pre_bytes + 1;
	else if (fifo_data_wr)
		packd_len <= pre_bytes;
`ifdef	FORMAL
	always @(*)
	if (!packd_valid)
		assert(packd_len == pre_bytes);
	always @(*)
	if (packd_valid && !packd_eop)
		assert(pre_bytes == packd_len);
`endif
	// }}}

	// packd_eop_addr
	// {{{
	// Points to the first address of where the next packet will start
	//   Doesn't update until the end of the last packet is accepted.
	// Hence, while a packet is building, this points to the first address
	// of the current packet.
	initial	packd_eop_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		packd_eop_addr <= 0;
	else if (i_soft_reset)
		packd_eop_addr <= 0;
	else if (fifo_data_wr && packd_eop)
		packd_eop_addr <= packd_addr+1;
	// }}}

	// packd_addr, the write address pointer
	// {{{
	always @(*)
	begin
		next_packd_addr = packd_addr;
		if (fifo_data_wr)
			// On any data write, increment our write data address.
			// Increment by two at the end of the packet, so
			// provide room for the packet length word
			next_packd_addr = packd_addr + (packd_eop ? 2:1);

		if (s_abort || pre_aborting)
			// Restart the packet data one word past the start
			// word of the packet
			next_packd_addr = packd_eop_addr + 1;

		if (!S_AXI_ARESETN || i_soft_reset)
			next_packd_addr = 1;
	end

	initial	packd_addr = 1;
	always @(posedge S_AXI_ACLK)
		packd_addr <= next_packd_addr;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert(packd_addr != packd_eop_addr);
`endif
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step two: Arbitrate who writes to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// wr_state
	// {{{
	//
	// wr_state is aligned w/ the interface w/ packd_valid and fifo_data_wr
	//
	initial	wr_state = FSM_DATA;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_soft_reset)
		wr_state <= FSM_DATA;
	else if (w_wr && S_AXIN_LAST)
		wr_state <= FSM_LAST;
	else if (fifo_wr)
	begin
		case(wr_state)
		FSM_LAST:	wr_state <= FSM_ADDR;
		FSM_ADDR:	wr_state <= FSM_DATA;
		// FSM_DATA:
		default:	wr_state <= FSM_DATA;
		endcase
	end

`ifdef	FORMAL
	always @(*)
	case(wr_state)
	FSM_DATA: begin end
	FSM_LAST: begin end
	FSM_ADDR: begin end
	default:	assert(0);
	endcase

	reg	[LGFLEN:0]	next_eop_addr, next_eop_len,tmp_eop_len;

	always @(*)
		next_eop_addr = 1 + tmp_eop_addr + tmp_len[M_DW-1:AXISLSB]
				+ ((tmp_len[AXISLSB-1:0] != 0) ? 1 : 0);

	always @(*)
		next_eop_len = next_eop_addr - rd_addr;

	always @(*)
		tmp_eop_len = tmp_eop_addr - rd_addr;

	always @(*)
	if (S_AXI_ARESETN && wr_state == FSM_ADDR)
	begin
		assert(tmp_len > 0);
		assert(packd_eop_addr == next_eop_addr);	// !!!!
		if (pre_bytes == 4)
			assert(packd_valid);
		assert(packd_len <= 4);
		assert(pre_bytes <= 4);

		assert(tmp_eop_len  <= FLEN);
		assert(next_eop_len <= FLEN);
	end

	always @(*)
	if (S_AXI_ARESETN)
		assert((wr_state == FSM_LAST) == packd_eop);

	//
	// RD_ADDR ... TMP_EOP_ADDR, (DATA), PACKED_EOP_ADDR, (DATA), PACKD_ADDR
`endif
	// }}}

	//
	// packd_* yields to mem_*
	//	packd_valid && fifo_data_wr : packd_* data fields
	//	=> mem_wr : mem_data, mem_addr
	//

	// tmp_len : Hold on to packd_len while packd* goes on to next packet
	// {{{
	initial	tmp_len = 0;
	always @(posedge S_AXI_ACLK)
	if (packd_valid && fifo_data_wr)
		tmp_len <= packd_len;
	// }}}

	// tmp_eop_addr : Hold onto packd_eop_data while packd* goes on to nxt
	// {{{
	initial	tmp_eop_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		tmp_eop_addr <= 0;
	else if (i_soft_reset)
		tmp_eop_addr <= 0;
	else if (wr_state != FSM_ADDR)
		tmp_eop_addr <= packd_eop_addr;
	// }}}

	// mem_data : Merge data from the two streams
	// {{{
	// Packets consist of a message length, followed by message data.
	// 1. Write data to a packet
	// 2. Write the last data to the packet
	// 3. Write zero following the packet
	// 4. Write the message length associated with the packet.
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mem_data <= 0;
	else if (wr_state == FSM_ADDR)
		mem_data <= tmp_len+4;
	else if (packd_valid)
		mem_data <= packd_data;
	else
		mem_data <= 0;
	// }}}

	// mem_addr : Merge address from the two streams
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_soft_reset)
		mem_addr <= 0;
	else if (wr_state == FSM_ADDR)
		mem_addr <= tmp_eop_addr[LGFLEN-1:0];
	else if (packd_valid)
		mem_addr <= packd_addr[LGFLEN-1:0];
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step three: Actually write to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// wr_fill
	// {{{
	// wr_fill = packd_addr - rd_addr;
	initial	wr_fill = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || i_soft_reset)
		wr_fill <= 1;
	else if (w_rd)
		wr_fill <= next_packd_addr - rd_addr - 1;
	else
		wr_fill <= next_packd_addr - rd_addr;
	// }}}

	// r_full
	// {{{
	// This is actually registered, since this will turn into the test:
	//	r_full = wr_fill[LGFLEN];
	assign	r_full = (wr_fill >= FLEN);
	// }}}

	// fifo_wr, fifo_data_wr, and fifo_stall flags
	// {{{
	assign	fifo_wr = !r_full && (packd_valid || wr_state == FSM_ADDR);
	assign	fifo_data_wr = !r_full && packd_valid
			&& (wr_state == FSM_DATA || wr_state == FSM_LAST);
	assign	fifo_stall = (packd_valid && (r_full || wr_state != FSM_DATA));

`ifdef	FORMAL
	always @(*)
	if (!fifo_wr)
	begin
		assert(!fifo_stall || r_full);
	end else if (fifo_data_wr)
	begin
		assert(!fifo_stall || wr_state == FSM_LAST);
	end else if (packd_valid)
		assert(fifo_stall);
`endif
	// }}}

	// mem_wr
	// {{{
	initial	mem_wr = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		mem_wr <= 1;
	else if (i_soft_reset)
		mem_wr <= 0;
	else
		mem_wr <= fifo_wr;
	// }}}

	// Write to memory
	// {{{
	initial	begin
		for(ik=0; ik<(1<<LGFLEN); ik=ik+1)
			mem[ik] = 0;
	end

	always @(posedge S_AXI_ACLK)
	if (mem_wr)
		mem[mem_addr[LGFLEN-1:0]] <= mem_data;
	// }}}

	// advance_mem - A new packet is now being written to the FIFO
	// {{{
	initial	advance_mem = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		advance_mem <= 0;
	else if (i_soft_reset)
		advance_mem <= 0;
	else
		advance_mem <= fifo_wr && wr_state == FSM_ADDR;
`ifdef	FORMAL
	always @(*)
	if (advance_mem)
		assert(mem_wr);
`endif
	// }}}
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Step four: Read out into the stream
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// rd_addr, the read address pointer
	// {{{
	initial	rd_addr = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		rd_addr <= 0;
	else if (i_soft_reset)
		rd_addr <= 0;
	else if (w_rd)
		rd_addr <= rd_addr + 1;
	// }}}

	// r_empty
	// {{{
	assign	next_rd_addr = rd_addr + 1;
	initial	r_empty = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_empty <= 1'b1;
	else if (i_soft_reset)
		r_empty <= 1'b1;
	else casez({ advance_mem, w_rd })
	2'b00: begin end // r_empty <= r_empty <= (rd_addr == packd_eop_addr);
	2'b01: r_empty <= (next_rd_addr == tmp_eop_addr);
	2'b1?: r_empty <= 1'b0;
	endcase
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
		assert(r_empty == (rd_addr == tmp_eop_addr));
`endif
	// }}}

	// M_AXI_TVALID
	// {{{
	assign	M_AXI_TVALID = !r_empty;
	// }}}

	// M_AXI_TDATA: Read from the FIFO
	// {{{
	generate if (OPT_ASYNC_READ)
	begin : ASYNCHRONOUS_READ
		// M_AXI_TDATA
		// {{{
		assign	M_AXI_TDATA = mem[rd_addr[LGFLEN-1:0]];
		// }}}
	end else begin : SYNCHRONOUS_MEM_READ
		// {{{
		reg			bypass;
		wire	[LGFLEN-1:0]	w_addr;
		reg	[M_DW-1:0]	bypass_mem, r_mem;

		assign	w_addr = rd_addr[LGFLEN-1:0] + ((w_rd) ? 1:0);

		always @(posedge S_AXI_ACLK)
		begin
			bypass <= mem_wr && r_empty;
			if (w_rd && w_addr == tmp_eop_addr[LGFLEN-1:0])
				bypass <= 1;
		end

		always @(posedge S_AXI_ACLK)
		// if (mem_wr && r_empty)
			bypass_mem <= mem_data;

		always @(posedge S_AXI_ACLK)
			r_mem <= mem[w_addr];

		assign	M_AXI_TDATA = (bypass) ? bypass_mem : r_mem;
`ifdef	FORMAL
		(* anyconst *) reg [LGFLEN-1:0]	fc_addr;
		reg [M_DW-1:0]	f_mem_data;
		reg		f_in_memory;

		always @(*)
		if (!S_AXI_ARESETN)
			assume(f_mem_data == mem[fc_addr]);

		always @(*)
		if (S_AXI_ARESETN)
			assert(f_mem_data == mem[fc_addr]);

		always @(posedge S_AXI_ACLK)
		if (mem_wr && mem_addr[LGFLEN-1:0] == fc_addr)
			f_mem_data <= mem_data;

		always @(posedge S_AXI_ACLK)
		if (M_AXI_TVALID && rd_addr[LGFLEN-1:0] == fc_addr)
			assert(M_AXI_TDATA == f_mem_data);
`endif
		// }}}
	end endgenerate
	// }}}
	// }}}

	// Make Verilator happy
	// {{{
	// verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0 };
	// verilator lint_on  UNUSED
	// }}}
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// FORMAL METHODS
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
`ifdef	FORMAL

//
// Assumptions about our input(s)
//
//
`ifdef	SFIFO
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	reg			f_past_valid;
	wire	[LGFLEN:0]	f_fill, m_fill, p_fill; // f_next;
	wire			f_full, m_empty; // f_empty, p_empty
	reg	[M_DW-1:0]	tmp_len_words;
	reg	[M_DW-1:0]	packd_len_words;
	reg	[LGFLEN:0]	packd_eop_from_tmp;
	wire	[10:0]	faxin_swords;
	wire	[11:0]	faxin_spkts;
	wire	[LGFLEN:0]	packd_len_addr;


	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	faxin_slave #(
		// {{{
		.DATA_WIDTH(BW),
		.MIN_LENGTH(0)
		// }}}
	) faxins (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		//
		.S_AXIN_VALID(S_AXIN_VALID), .S_AXIN_READY(S_AXIN_READY),
		.S_AXIN_DATA(S_AXIN_DATA), .S_AXIN_LAST(S_AXIN_LAST),
		.S_AXIN_ABORT(S_AXIN_ABORT),
		//
		.f_stream_word(faxin_swords),
		.f_packets_rcvd(faxin_spkts)
		// }}}
	);

	// AXI stream (master) properties
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN) || $past(i_soft_reset))
	begin
		assert(!M_AXI_TVALID);
	end else if ($past(M_AXI_TVALID && !M_AXI_TREADY))
	begin
		assert(M_AXI_TVALID);
		assert($stable(M_AXI_TDATA));
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assertions about our flags and counters
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// We have three FIFO levels here that are important to us:
	//
	// 1. Master stream
	//	This level describes a complete packet that is currently being
	//	read out.  If no complete packet is available, this level is
	//	empty--even if the FIFO isn't empty.
	//
	// 2. Entire FIFO
	// 3. The partial packet level.  This is the partially received packet,
	//	between entry and the last end of packet marker.  The master
	//	stream is not allowed to read from this partial FIFO.
	//

	// Fill/empty at the stream master level
	// {{{
	// This is the fill between the last packet accepted and the full FIFO
	// size
	assign	m_fill  =  tmp_eop_addr - rd_addr;
	assign	m_empty = (tmp_eop_addr == rd_addr);
	// }}}

	// Fill/empty at the slave/pkt level
	// {{{
	assign	f_fill  =  packd_addr - rd_addr;
	// assign	f_empty = (tmp_eop_addr == rd_addr);
	assign	f_full  = (f_fill >= FLEN);

	always @(*)
	begin
		assert(f_fill == wr_fill);
		assert(f_full == r_full);
	end
	// }}}

	// Fill/empty at the partial pkt level
	// {{{
	// This is where we are building a new packet.  It is our partial fill.
	assign	p_fill  =  packd_addr - packd_eop_addr;
	always @(*)
	begin
		if (packd_valid)
			packd_len_words = packd_len + (1<<AXISLSB)-1;
		else
			packd_len_words = packd_len;
		packd_len_words[AXISLSB-1:0] = 0;
		packd_len_words = packd_len_words + (1<<AXISLSB);
	end
	assign	packd_len_addr = packd_len_words[AXISLSB +: (LGFLEN + 1)];
	// }}}

	// packd_eop_from_tmp
	// {{{
	always @(*)
	begin
		tmp_len_words = tmp_len + (1<<AXISLSB)-1;
		tmp_len_words[AXISLSB-1:0] = 0;
		tmp_len_words = tmp_len_words + (1<<AXISLSB);

		packd_eop_from_tmp = tmp_eop_addr
				+ tmp_len_words[AXISLSB +: LGFLEN];
	end
	// }}}

	// {{{
	always @(*)
		assert( (wr_state == FSM_LAST) == (packd_valid && packd_eop));

	always @(*)
	begin
		assert(f_fill <= FLEN + ((wr_state == FSM_ADDR) ? 1:0));
		assert(p_fill <= FLEN);
		assert(p_fill >  0);
		assert(m_fill <= FLEN);
		if (wr_state == FSM_ADDR)
			assert(p_fill <= 2);

		if (m_fill == 0)
			assert(r_empty);

		assert(p_fill <= f_fill);
		assert(m_fill <= f_fill);

		assert(pre_bytes <= (1<<(LGFLEN+AXISLSB)));
		if (packd_valid)
			assert(packd_eop || pre_bytes > 0);

		assert(packd_len[M_DW-1:(AXISLSB+LGFLEN+1)] == 0);
		assert(tmp_len[M_DW-1:(AXISLSB+LGFLEN+1)] == 0);

		if (packd_valid && packd_eop)
		begin
			assert(pre_bytes == 0);
			assert(packd_len > 0);
		end

		assert(packd_len_addr
			== p_fill[LGFLEN:0] + (packd_valid ? 1:0));


		if (S_AXI_ARESETN && wr_state != FSM_ADDR)
		begin
			if (packd_eop)
			begin
				assert(pre_bytes == 0);
			end
		end else if (S_AXI_ARESETN && wr_state == FSM_ADDR)
		begin
			assert(pre_bytes <= (1<<AXISLSB));
		end
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Formal contract: (Twin write test -- NOT YET INCLUDED)
	// {{{
	// If you write two values in succession, you should be able to read
	// those same two values in succession some time later.
	//
	////////////////////////////////////////////////////////////////////////
	//
	//
`ifdef	TWIN_WRITE
	(* anyconst *)	reg	[LGFLEN:0]	f_first_addr;
			wire	[LGFLEN:0]	f_second_addr;
			reg	[BW:0]	f_first_data, f_second_data;
			wire	[BW:0]	f_eop_data;

	reg			f_first_addr_in_fifo,  f_first_in_fifo;
	reg			f_second_addr_in_fifo, f_second_in_fifo;
	reg			f_eop_addr_in_fifo;
	reg	[LGFLEN:0]	f_distance_to_first, f_distance_to_second,
				f_distance_to_eop;
	wire	[LGFLEN:0]	f_first_to_eop, f_second_to_eop;

	assign	f_second_addr = f_first_addr + 1;

	// f_distance_to_first, f_first_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_first = (f_first_addr - rd_addr);
		f_first_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_first < f_fill))
			f_first_addr_in_fifo = 1;
	end
	// }}}

	// f_distance_to_second, f_second_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_second = (f_second_addr - rd_addr);
		f_second_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_second < f_fill))
			f_second_addr_in_fifo = 1;
	end
	// }}}

	// f_distance_to_eop, f_eop_addr_in_fifo
	// {{{
	always @(*)
	begin
		f_distance_to_eop = (eop_addr - rd_addr);
		f_eop_addr_in_fifo = 0;
		if ((f_fill != 0) && (f_distance_to_eop < f_fill))
			f_eop_addr_in_fifo = 1;
	end
	// }}}

	// f_first_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr && wr_addr == f_first_addr)
		f_first_data <= { S_AXIN_LAST, S_AXIN_DATA };
	// }}}

	// f_second_data
	// {{{
	always @(posedge S_AXI_ACLK)
	if (w_wr && wr_addr == f_second_addr)
		f_second_data <= { S_AXIN_LAST, S_AXIN_DATA };
	// }}}

	// f_first_data checks
	// {{{
	always @(*)
	if (f_first_addr_in_fifo)
		assert(mem[f_first_addr[LGFLEN-1:0]] == f_first_data);
	always @(*)
	if (f_first_addr_in_fifo && lastv && f_first_addr == eop_addr)
		assert(mem[f_first_addr[LGFLEN-1:0]][BW]);
	always @(*)
		f_first_in_fifo = (f_first_addr_in_fifo && (mem[f_first_addr[LGFLEN-1:0]] == f_first_data));
	// }}}

	// f_second_data checks
	// {{{
	always @(*)
	if (f_second_addr_in_fifo)
		assert(mem[f_second_addr[LGFLEN-1:0]] == f_second_data);
	always @(*)
	if (f_second_addr_in_fifo && lastv && f_second_addr == eop_addr)
		assert(mem[f_second_addr[LGFLEN-1:0]][BW]);

	always @(*)
		f_second_in_fifo = (f_second_addr_in_fifo && (mem[f_second_addr[LGFLEN-1:0]] == f_second_data));
	// }}}

	// EOP checks
	// {{{
	assign	f_first_to_eop  = (eop_addr - f_first_addr);
	assign	f_second_to_eop = (eop_addr - f_second_addr);

	assign	f_eop_data = mem[eop_addr[LGFLEN-1:0]];

	always @(*)
	if (S_AXI_ARESETN && lastv)
	begin
		assert(f_eop_addr_in_fifo);
		assert(f_eop_data[BW]);

		if (f_first_in_fifo && f_first_data[BW])
			assert(f_first_to_eop < (1<<LGFLEN));
		if (f_second_in_fifo && f_second_data[BW])
			assert(f_second_to_eop < (1<<LGFLEN));
	end
	// }}}

	// Twin write state machine
	// {{{
	always @(posedge S_AXI_ACLK)
	if (f_past_valid && $past(S_AXI_ARESETN))
	begin
		case({$past(f_first_in_fifo), $past(f_second_in_fifo)})
		2'b00: begin
				// {{{
				if ($past(w_wr && (!w_rd || !r_empty))
					&&($past(wr_addr == f_first_addr)))
					assert(f_first_in_fifo);
				else
					assert(!f_first_in_fifo);
				//
				// The second could be in the FIFO, since
				// one might write other data than f_first_data
				//
				// assert(!f_second_in_fifo);
			end
			// }}}
		2'b01: begin
				// {{{
				assert(!f_first_in_fifo);
				if ($past(w_rd && (rd_addr==f_second_addr)))
					assert(!f_second_in_fifo);
				else
					assert(f_second_in_fifo);
			end
			// }}}
		2'b10: begin
				// {{{
				if ($past(w_wr)
					&&($past(wr_addr == f_second_addr)))
					assert(f_second_in_fifo);
				else
					assert(!f_second_in_fifo);
				if ((!$past(S_AXIN_ABORT)) // || $past(lastv))
					&& ($past(!w_rd ||(rd_addr != f_first_addr))))
					assert(f_first_in_fifo);
			end
			// }}}
		2'b11: begin
			// {{{
				if (!$past(S_AXIN_ABORT) && !M_AXI_TABORT) // || $past(lastv))
				begin
					assert(f_second_in_fifo);
					if ($past(!w_rd ||(rd_addr != f_first_addr)))
					begin
						assert(f_first_in_fifo);
						if (rd_addr == f_first_addr)
							assert({ M_AXI_TLAST, M_AXI_TDATA } == f_first_data);
					end else begin
						assert(!f_first_in_fifo);
						assert({ M_AXI_TLAST, M_AXI_TDATA } == f_second_data);
					end
				end
			end
			// }}}
		endcase
	end
	// }}}

`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	reg	cvr_was_full;

	initial	cvr_was_full = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_was_full <= 0;
	else if (!S_AXIN_READY)
		cvr_was_full <= 1;

`ifdef	SFIFO
	always @(posedge S_AXI_ACLK)
		cover($fell(f_empty));

	always @(posedge S_AXI_ACLK)
		cover($fell(!M_AXI_TREADY));

	always @(posedge S_AXI_ACLK)
		cover(cvr_was_full && f_empty);

	always @(posedge S_AXI_ACLK)
		cover($past(!S_AXIN_READY,2)&&(!$past(!S_AXIN_READY))&&(!S_AXIN_READY));

	always @(posedge S_AXI_ACLK)
	if (f_past_valid)
		cover($past(!M_AXI_TREADY,2)&&(!$past(!M_AXI_TREADY))&& !M_AXI_TREADY);
`endif
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	//	Simplifying assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// always @(*) assume(!S_AXIN_ABORT);
	// always @(*) assume(!pre_aborting);
	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0, faxin_swords, faxin_spkts };
	// Verilator lint_on  UNUSED
	// }}}
`endif // FORMAL
// }}}
endmodule
