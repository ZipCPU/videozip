////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/netdbgtx.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Assembles the output of a debugging packet request into a
//		memory first, and then forwards those memory values to a
//	packet to an (external) UDP converter.
//
// Options:
//	OPT_CONSOLE: I'd like to add an optional console port to this design.
//		The way it would work would be to append to any return packet
//		console data information until either the console is drained,
//		or the packet is full.  (This hasn't yet been implemented.)
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
module	netdbgtx #(
		parameter [7:0]	STUFF_BYTE = 8'h00
		// parameter [0:0] OPT_CONSOLE = 1'b0
	) (
		// {{{
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		//
		// Debug global wires
		// {{{
		input	wire		i_sync,
		input	wire	[15:0]	i_gpio,
		input	wire		i_repeat_stb,
		input	wire	[15:0]	i_hostid,
		// }}}
		// The payload processors input
		// {{{
		input	wire		S_AXI_TVALID,
		output	wire		S_AXI_TREADY,
		input	wire	[7:0]	S_AXI_TDATA,
		input	wire		S_AXI_TLAST,
		// }}}
		// (Optional) console input
		// {{{
		// input	wire		S_CON_TVALID,
		// output	wire		S_CON_TREADY,
		// input	wire	[7:0]	S_CON_TDATA,
		//	Since there are no packet boundaries to raw console
		//	data, there will be no last to the data--it's just
		//	there or it isn't
		// }}}
		// Output to the UDP packet generator
		// {{{
		output	wire		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	wire	[31:0]	M_AXIN_DATA,
		output	wire		M_AXIN_LAST,
		output	wire		M_AXIN_ABORT,
		// }}}
		output	wire		o_overflow,
		output	wire [31:0]	o_debug
		// }}}
	);

	// Local declarations
	// {{{
	// LGMEM: The log (base two) of the mem size in bytes
	localparam		LGMEM = 11;
	reg	[31:0]		mem	[0:((1<<(LGMEM-2))-1)];

	reg			mem_we, overflow;
	wire			will_overflow;
	reg	[LGMEM-1:0]	mem_waddr, mem_len, in_addr;
	reg	[31:0]		mem_wdata;
	reg	[LGMEM-3:0]	mem_raddr, w_mem_raddr;
	reg			mem_last;

	reg	[2:0]		pkt_state;

	localparam	[2:0]	TX_IDLE        = 3'b000,
				TX_RPT_HEADER  = 3'b001,
				TX_RPT_NXTHDR  = 3'b010,
				TX_RPT_PAYLOAD = 3'b011,
				TX_NEW_HEADER  = 3'b100,
				TX_NEW_NXTHDR  = 3'b101,
				TX_NEW_PAYLOAD = 3'b110;

	reg	[15:0]	dbg_pkt_counter, last_host_id, prior_host_id;
	reg		m_valid, m_last;
	reg	[31:0]	m_data, mem_rdata;
	reg		r_busy, r_loaded;

	reg		no_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Copy the incoming packet to memory
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	will_overflow = (mem_waddr[LGMEM-1:0] >= {(LGMEM){1'b1}} -6 );

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		mem_we <= 1'b0;
		mem_waddr <= 0;
		mem_last  <= 1;
		mem_wdata <= {(4){STUFF_BYTE}};
		in_addr <= 0;
		// }}}
	end else if (S_AXI_TVALID && S_AXI_TREADY)
	begin
		// {{{
		mem_we <= !overflow;
		mem_last <= 0;
		in_addr   <= in_addr + 1;
		mem_waddr <= in_addr;
		if (mem_last)
		begin
			// This is the first word of the packet
			mem_wdata <= { S_AXI_TDATA, {(3){STUFF_BYTE}} };
		end else begin
			// Every subsequent word
			case(in_addr[1:0])
			2'b00: mem_wdata <= { S_AXI_TDATA, {(3){STUFF_BYTE}} };
			2'b01: mem_wdata[23:0] <= { S_AXI_TDATA, {(2){STUFF_BYTE}} };
			2'b10: mem_wdata[15:0] <= { S_AXI_TDATA, {(1){STUFF_BYTE}} };
			2'b11: mem_wdata[7:0]  <= S_AXI_TDATA;
			endcase
		end

		if (S_AXI_TLAST)
		begin
			mem_len <= in_addr + 4;
			mem_len[1:0] <= 2'b00;
			mem_last <= 1;
			in_addr  <= 0;
		end
		// }}}
	end else begin
		// {{{
		mem_we <= 0;
		mem_waddr <= in_addr;
		if (mem_last)
		begin
			in_addr <= 0;
			mem_waddr <= 0;
			mem_wdata <= {(4){STUFF_BYTE}};
		end
		// }}}
	end

	always @(posedge S_AXI_ACLK)
	if (mem_we)
		mem[mem_waddr[LGMEM-1:2]] <= mem_wdata;

	// overflow
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		overflow  <= 0;
	else if (!r_busy && !M_AXIN_VALID && i_sync && mem_last)
		// Reset overflow indicator on a sync request
		overflow <= 1'b0;
	else if (S_AXI_TVALID && S_AXI_TREADY && will_overflow && !S_AXI_TLAST)
		overflow <= 1'b1;

	assign	o_overflow = overflow;
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Add a header, and copy the incoming packet to the output
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(*)
	begin
		w_mem_raddr = mem_raddr;
		if (m_valid && M_AXIN_READY && pkt_state == TX_RPT_PAYLOAD)
			w_mem_raddr = w_mem_raddr + 1;
	end

	always @(posedge S_AXI_ACLK)
		mem_rdata <= mem[w_mem_raddr];

	assign	S_AXI_TREADY = (overflow && !mem_last)
			|| (r_busy && !no_data && pkt_state == TX_NEW_PAYLOAD
					&& (!M_AXIN_VALID || M_AXIN_READY));

	// dbg_pkt_counter
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		dbg_pkt_counter <= 0;
	else if (pkt_state == TX_NEW_NXTHDR && (!M_AXIN_VALID || M_AXIN_READY))
		dbg_pkt_counter <= dbg_pkt_counter + 1;
	// }}}

	// last_host_id, prior_host_id
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		last_host_id <= 0;
		prior_host_id <= 0;
	end else if (i_sync)
	begin
		last_host_id <= 0;
		prior_host_id <= 0;
	end else if (pkt_state == TX_NEW_HEADER
					&& (!M_AXIN_VALID || M_AXIN_READY))
	begin
		last_host_id  <= i_hostid;
		prior_host_id <= last_host_id;
	end
	// }}}

	// no_data
	// {{{
	// True if this is a sync only packet, with no data payload
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		no_data <= 0;
	else if (!r_busy)
	begin
		no_data <= 1'b0;
		if (!M_AXIN_VALID && i_sync && (!overflow || mem_last))
			no_data <= 1'b1;
	end
	// }}}

	// pkt_state, m_valid, m_data, m_last, mem_raddr
	// {{{
	initial	pkt_state = TX_IDLE;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		pkt_state <= TX_IDLE;
		m_valid <= 1'b0;
		mem_raddr <= 0;
		// }}}
	end else if (!r_busy)
	begin	// TX_IDLE -> TX_RPT_HEADER | TX_NEW_HEADER
		// {{{
		pkt_state <= TX_IDLE;
		mem_raddr <= 0;

		if (M_AXIN_READY)
			m_valid <= 1'b0;

		if (M_AXIN_VALID)
		begin
		end else if (i_repeat_stb)
		begin
			if (!overflow && r_loaded)
				pkt_state <= TX_RPT_HEADER;
		end else if (i_sync && (!overflow || mem_last))
			pkt_state <= TX_NEW_HEADER;
		else if (S_AXI_TVALID && !overflow)
			pkt_state <= TX_NEW_HEADER;
		// }}}
	end else if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		// {{{
		m_valid <= 0;
		case(pkt_state)
		TX_RPT_HEADER: begin	// -> TX_RPT_NXTHDR
			// {{{
			m_valid <= 1;
			pkt_state <= TX_RPT_NXTHDR;
			end
			// }}}
		TX_RPT_NXTHDR: begin	// -> TX_RPT_PAYLOAD
			// {{{
			m_valid <= 1;
			mem_raddr <= 0;
			pkt_state <= TX_RPT_PAYLOAD;
			end
			// }}}
		TX_RPT_PAYLOAD: begin	// -> (*) -> TX_IDLE (??)
			// {{{
			m_valid <= 1;
			mem_raddr <= mem_raddr + 1;
			if (w_mem_raddr + 1 >= mem_len[LGMEM-1:2])
			begin
				pkt_state <= TX_IDLE;
			end end
			// }}}
		TX_NEW_HEADER: begin	// -> TX_NEW_NXTHDR
			// {{{
			m_valid <= 1;
			pkt_state <= TX_NEW_NXTHDR;
			end
			// }}}
		TX_NEW_NXTHDR: begin	// -> TX_NEW_PAYLOAD
			// {{{
			m_valid <= 1;
			pkt_state <= TX_NEW_PAYLOAD;
			if (no_data)
				pkt_state <= TX_IDLE;
			end
			// }}}
		TX_NEW_PAYLOAD: begin	// -> (*) -> TX_IDLE
			// {{{
			m_valid <= S_AXI_TLAST || (in_addr[1:0] == 2'b11)
				|| will_overflow;
			if (!S_AXI_TVALID || overflow)
				m_valid <= 0;

			if ((S_AXI_TVALID && S_AXI_TLAST)
				|| (S_AXI_TVALID && will_overflow))
			begin
				pkt_state <= TX_IDLE;
			end end
			// }}}
		default: begin
			// {{{
			pkt_state <= TX_IDLE;
			m_valid <= 0;
			end
			// }}}
		endcase
		// }}}
	end
	// }}}

	// m_data, m_last
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		m_last  <= 0;
		case(pkt_state)
		TX_RPT_HEADER: m_data  <= { last_host_id, i_gpio };
		TX_RPT_NXTHDR: m_data  <= { prior_host_id, dbg_pkt_counter };
		TX_RPT_PAYLOAD: begin	// -> (*) -> TX_IDLE (??)
			// {{{
			m_data  <= mem_rdata;
			m_last  <= (w_mem_raddr + 1 >= mem_len[LGMEM-1:2]);
			end
			// }}}
		TX_NEW_HEADER: m_data  <= { i_hostid, i_gpio };
		TX_NEW_NXTHDR: begin	// -> TX_NEW_PAYLOAD
			// {{{
			m_data  <= { prior_host_id, dbg_pkt_counter };
			if (no_data)
				m_last  <= 1'b1;
			end
			// }}}
		TX_NEW_PAYLOAD: begin	// -> (*) -> TX_IDLE
			// {{{
			m_last  <= S_AXI_TLAST || will_overflow;

			case(in_addr[1:0])
			2'b00: m_data <= { S_AXI_TDATA, {(3){STUFF_BYTE}} };
			2'b01: m_data <= { mem_wdata[31:24], S_AXI_TDATA, {(2){STUFF_BYTE}} };
			2'b10: m_data <= { mem_wdata[31:16], S_AXI_TDATA, {(1){STUFF_BYTE}} };
			2'b11: m_data <= { mem_wdata[31:8], S_AXI_TDATA };
			endcase end
			// }}}
		default: begin end
		endcase
	end
	// }}}

	// r_busy
	// {{{
	initial	r_busy = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_busy <= 0;
	else if (!r_busy)
	begin	// -> TX_RPT_HEADER | TX_NEW_HEADER
		// {{{
		if (M_AXIN_VALID)
		begin
			// r_busy  <= 1'b0;
		end else if (i_repeat_stb)
			r_busy <= r_loaded && !overflow;
		else if (i_sync && (!overflow || mem_last))
			r_busy <= 1;
		else if (S_AXI_TVALID && !overflow)
			r_busy <= 1;
		// }}}
	end else if (!M_AXIN_VALID || M_AXIN_READY)
	begin
		// {{{
		// r_busy <= 1;
		case(pkt_state)
		TX_RPT_HEADER: begin end
		TX_RPT_NXTHDR: begin end
		TX_RPT_PAYLOAD: if (w_mem_raddr + 1 >= mem_len[LGMEM-1:2])
				r_busy    <= 0;
		TX_NEW_HEADER: begin end
		TX_NEW_NXTHDR: if (no_data)
				r_busy <= 1'b0;
		TX_NEW_PAYLOAD: if (S_AXI_TVALID && (S_AXI_TLAST || will_overflow))
				r_busy  <= 1'b0;
		default:
			r_busy <= 0;
		endcase
		// }}}
	end
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN)
	begin
		assert(r_busy == (pkt_state != TX_IDLE));
		if(overflow)
			assert(!r_busy);
	end
`endif
	// }}}

	// r_loaded
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		r_loaded <= 1'b0;
	else if ((i_sync && !r_busy) || (S_AXI_TVALID && S_AXI_TREADY && !S_AXI_TLAST && will_overflow))
		r_loaded <= 1'b0;
	else if (S_AXI_TVALID && S_AXI_TREADY && S_AXI_TLAST && !overflow
			&& !will_overflow)
		r_loaded <= 1'b1;
`ifdef	FORMAL
	always @(*)
	if (S_AXI_ARESETN && overflow)
		assert(!r_loaded);
`endif
	// }}}

	assign	M_AXIN_VALID = m_valid;
	assign	M_AXIN_DATA  = m_data;
	assign	M_AXIN_LAST  = m_last;
	assign	M_AXIN_ABORT = 1'b0;
	// }}}

	assign	o_debug = {
		(i_sync || i_repeat_stb || S_AXI_TVALID),
		i_sync, i_repeat_stb, r_busy, o_overflow,
		pkt_state,
		M_AXIN_VALID, M_AXIN_READY, M_AXIN_LAST, M_AXIN_ABORT,
			mem_waddr[8:0],
		S_AXI_TVALID, S_AXI_TREADY, S_AXI_TLAST, S_AXI_TDATA
		};

	// Keep Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, mem_len[1:0] };
	// Verilator lint_on  UNUSED
	// }}}
endmodule
