////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/pktconsole.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Accepts console data as input, produces packets containing that
//		same console data.  For use with designs having a network port
//	but no console port.  TCP would be better, yes, but this is for hardware
//	use before the CPU has established any TCP connections.  Therefore, this
//	design is intended to be somewhat redundant / fault tolerant.
//
//	The general concept is that we always produce packets containing the
//	last *N* characters (for however many *N* is).  As new data is written
//	to the console, it overwrites an internal circular buffer.  Further, a
//	24-bit pointer is maintained to describe where we are in our output
//	stream.  As new values enter, the pointer is incremented.
//
//	We then wait for a request to generate a packet.  This request will
//	be generated externally, by whatever controls our context.  If the
//	packet request doesn't come often enough, data will be lost.  This
//	is understood.  Requests come with an amount of data to be produced.
//	This is to allow console packets to be appended to packets that may have
//	already been assembled for other purpoess (such as the debug packet
//	stream) if necessary.
//
//	Other than redundancy, that is other than by sending the same console
//	data multiple times, there is *NO* protection here against dropped
//	packets.  If you want that protection, implement a proper TCP stream
//	in software.
//
// Concept: Accepts a write data (AXI) stream of characters.  Then, upon
//	request and available packet size, generates a packet of console
//	characters.  There's protection against lost data.  If no packet
//	request arrives in time, characters may be lost.
//
//	While a packet is outgoing, the READY signal will be used to prevent
//	the FIFO from overwriting characters that have already been committed
//	to the packet.  Similarly, while the packet is outgoing, additional
//	characters added to the FIFO will be ignored.
//
//
//
// Packet frequency: Either ...
//	Packets frequency will be determined externally, and will likely be
//	one of:
//	- Every 1<<(LGFLEN-3) characters, or ...
//	- Every 125ms if the interface is otherwise idle
//	Or ... more frequent if something else generates the packets
//		For example, I'm still holding out the option of attaching
//		the console packets to the tail end of any debug packets.
//		In that case, the external debug packet controller will
//		determine when/if to send packets, and how much data may be
//		sent in each packet.
//
// Packet format:
//	0	First byte is always 8'h00
//	24'hLEN	Next 3-bytes are the position of the current character in
//		the buffer.  This will be the *LAST* character of the packet
//		EVEN IF other characters arrive in the meantime.
//	(CHDAT)	This will all be followed by the character data.  Unlike the
//		first character, there is no marking, other than the LAST
//		output tag, is provided to mark the last character in the
//		sequence.
//
//	If 24'hLEN is less than the desired packet length, the packet will
//		be truncated before the requested length.  If it is longer,
//		then the outgoing packet must match the requested size.
//
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
module pktconsole #(
		// {{{
		parameter		LGFIFO	= 12,
		parameter [0:0]		OPT_LOWPOWER = 1'b0,
		parameter [0:0]		OPT_SKIDBUFFER = 1'b0,
		parameter [LGFIFO-1:0]	MAXPKTLN = (1<<LGFIFO)-4
		// }}}
	) (
		// {{{
		input	wire			i_clk, i_reset,
		// Console input
		// {{{
		input	wire			S_CON_VALID,
		output	wire			S_CON_READY,
		input	wire	[7:0]		S_CON_DATA,
		// }}}
		// Packet request
		// {{{
		input	wire			i_req,
		output	wire			o_busy,
		// output wire o_req_busy = M_CON_VALID
		input	wire	[LGFIFO-1:0]	i_len,
		// }}}
		// Outgoing console packet data
		// {{{
		output	wire			M_CON_VALID,
		input	wire			M_CON_READY,
		output	wire	[7:0]		M_CON_DATA,
		output	wire			M_CON_LAST
		// }}}
		// }}}
	);

	// Local declarations
	// {{{
	wire			skd_valid, skd_ready;
	wire	[7:0]		skd_data;

	reg	[7:0]		mem	[0:(1<<LGFIFO)-1];

	reg	[LGFIFO-1:0]	space_available;
	reg			no_space;

	reg	[24:0]		wrposn;
	reg	[23:0]		rdposn;
	reg	[LGFIFO-1:0]	wraddr;
	reg	[LGFIFO-1:0]	rdstart, rdptr, rdend;
	reg	[2:0]		m_fsm;

	reg	[LGFIFO-1:0]	reqlen;

	reg	[7:0]		r_data;
	reg			r_dlast;
	reg			m_valid, m_last;
	reg	[7:0]		m_data;

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// (Optional) skidbuffer
	// {{{

	generate if (OPT_SKIDBUFFER)
	begin : GEN_SKIDBUFFER

		skidbuffer #(
			.OPT_LOWPOWER(OPT_LOWPOWER), .DW(8)
		) conskid (
			.i_clk(i_clk), .i_reset(i_reset),
			.i_valid(S_CON_VALID), .o_ready(S_CON_READY),
				.i_data(S_CON_DATA),
			.o_valid(skd_valid), .i_ready(skd_ready),
				.o_data(skd_data)
		);

	end else begin : NO_SKIDBUFFER

		assign	skd_valid = S_CON_VALID;
		assign	S_CON_READY = skd_ready;
		assign	skd_data  = S_CON_DATA;

	end endgenerate

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Write console data to the FIFO
	// {{{

	// wrposn
	// {{{
	// The top bit, bit 24, contains whether we've overflowed or not
	always @(posedge i_clk)
	if (i_reset)
		wrposn <= 0;
	else if (skd_valid && skd_ready)
	begin
		if (!wrposn[24])
			wrposn <= wrposn + 1;
		else
			wrposn[23:0] <= wrposn[23:0] + 1;
	end
	// }}}

	assign	wraddr = wrposn[LGFIFO-1:0];

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		mem[wraddr[LGFIFO-1:0]] <= skd_data;

	// space_available, no_space
	// {{{
	// These registers exist to allow data to be written to our FIFO
	// while we are producing a packet, while at the same time guaranteeing
	// that the new data will never overwrite the FIFO data required by the
	// packet currently being produced.
	always @(posedge i_clk)
	if (i_reset)
	begin
		space_available <= MAXPKTLN;
		no_space <= 0;
	end else if (!o_busy)
	begin
		if (OPT_LOWPOWER && !i_req)
			space_available <= MAXPKTLN;
		else
			// Verilator lint_off WIDTH
			space_available <= - reqlen
					- ((skd_valid && skd_ready) ? 1:0);
			// Verilator lint_on  WIDTH
		no_space <= 0;
	end else case({ skd_valid && skd_ready,
		M_CON_VALID && M_CON_READY && m_fsm == FSM_DATA })
	2'b10: begin
		space_available <= space_available - 1;
		no_space <= (space_available <= 1);
		end
	2'b01: begin
		space_available <= space_available + 1;
		no_space <= 1'b0;
		end
	default: begin end
	endcase
`ifdef	FORMAL
	wire	[LGFIFO-1:0]	f_newly_accepted, f_reserved;

	assign	f_newly_accepted = wrposn - rdposn;
	assign	f_reserved       = rdposn[LGFIFO-1:0] - rdptr;

	always @(*)
	if (!i_reset && o_busy && !M_CON_LAST && !m_dlast)
	begin
		assert(f_newly_accepted < (1<<LGFIFO));
		assert(space_available  < (1<<LGFIFO));
		assert(f_reserved > 0);
		assert(f_reserved <= MAXPKTLN);

		assert(f_newly_accepted + space_available < (1<<LGFIFO));
		assert(f_newly_accepted + space_available + f_reserved
							== (1<<LGFIFO));
	end
`endif
	// }}}

	assign	skd_ready = !M_CON_VALID || !no_space;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Handle incoming packet requests
	// {{{

	always @(*)
	begin
		reqlen = i_len;
		if (i_len >= MAXPKTLN)
			reqlen = MAXPKTLN;
		if (!wrposn[24]
			&& { {(24-LGFIFO){1'b0}}, i_len } >= wrposn[23:0])
			reqlen = wrposn[LGFIFO-1:0];
	end

	always @(posedge i_clk)
	if (i_reset)
	begin
		rdstart <= 0;
		rdposn  <= 0;
	end else if ((!OPT_LOWPOWER || i_req) && !o_busy)
	begin
		rdstart <= wrposn[LGFIFO-1:0] - reqlen[LGFIFO-1:0];

		rdposn <= wrposn[23:0];
	end

	assign	rdend = rdposn[LGFIFO-1:0]-1;
	assign	o_busy = M_CON_VALID;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Assemble the packet
	// {{{
	localparam	[2:0]	FSM_IDLE  = 3'b000,
				// FSM_PREFIX= 3'b001,
				FSM_POSN1 = 3'b001,
				FSM_POSN2 = 3'b010,
				FSM_POSN3 = 3'b011,
				FSM_DATA  = 3'b100;

	// rdptr
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		rdptr <= 0;
	else if (m_fsm <= FSM_POSN1)
		rdptr <= rdstart[LGFIFO-1:0];
	else if (M_CON_VALID && M_CON_READY)
		rdptr <= rdptr + 1;
	// }}}

	// r_data
	// {{{
	always @(posedge i_clk)
	if ((m_fsm <= FSM_POSN1) || M_CON_READY)
		r_data <= mem[rdptr];
	// }}}

	// r_dlast
	// {{{
	always @(posedge i_clk)
	if (i_reset || m_fsm <= FSM_POSN1)
		r_dlast <= 1'b0;
	else if (M_CON_READY)
		r_dlast <= (rdptr == rdend);
`ifdef	FORMAL
	always @(*)
	if (!i_reset && m_fsm > FSM_POSN1)
	begin
		assert(o_busy);
		assert(M_CON_VALID);
	end
`endif
	// }}}

	// m_fsm
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		m_fsm <= 0;
	else if (M_CON_VALID && M_CON_READY)
	begin
		if (M_CON_LAST)
			m_fsm <= FSM_IDLE;
		else if (m_fsm < FSM_DATA)
			m_fsm <= m_fsm + 1;
	end
	// }}}

	// m_valid
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		m_valid <= 1'b0;
	else if (i_req && !o_busy)
		m_valid <= 1'b1;
	else if (M_CON_VALID && M_CON_READY && M_CON_LAST)
		m_valid <= 1'b0;
	// }}}

	// m_data
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_req || !M_CON_VALID)
		m_data <= 8'h00;
	else if (M_CON_READY)
	begin
		case(m_fsm)
		FSM_IDLE:   m_data <= 8'h00;
		FSM_POSN1:  m_data <= rdposn[23:16];
		FSM_POSN2:  m_data <= rdposn[15: 8];
		FSM_POSN3:  m_data <= rdposn[ 7: 0];
		default:
			m_data <= r_data;
		endcase

		if (M_CON_LAST)
			m_data <= 8'h00;
	end
	// }}}

	// m_last
	// {{{
	always @(posedge i_clk)
	if (i_reset || i_req)
		m_last <= 1'b0;
	else if (M_CON_VALID && M_CON_READY)
	begin
		m_last <= 1'b0;
		if (rdstart == rdposn[LGFIFO-1:0] && m_fsm == FSM_POSN3)
			m_last <= 1'b1;
		if (r_dlast)
			m_last <= 1'b1;
	end
	// }}}

	assign	M_CON_VALID = m_valid;
	assign	M_CON_DATA  = m_data;
	assign	M_CON_LAST  = m_last;
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
	reg	f_last_valid;

	initial	f_past_valid = 1'b0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	////////////////////////////////////////////////////////////////////////
	//
	// AXI stream properties
	// {{{
	always @(posedge i_clk)
	if (!f_last_valid || $past(i_reset))
		assume(!S_CON_VALID);
	else if ($past(S_CON_VALID && !S_CON_READY))
	begin
		assume(S_CON_VALID);
		assume($stable(S_CON_DATA));
	end

	always @(posedge i_clk)
	if (!f_last_valid || $past(i_reset))
		assume(!i_req);
	else if ($past(i_req && o_busy))
	begin
		assume(i_req);
		assume($stable(i_len));
	end

	always @(*)
	if (i_req)
		assume(i_len > 0);

	always @(posedge i_clk)
	if (!f_last_valid || $past(i_reset))
		assert(!M_CON_VALID);
	else if ($past(M_CON_VALID && !M_CON_READY))
	begin
		assert(M_CON_VALID);
		assert($stable(M_CON_DATA));
		assert($stable(M_CON_LAST));
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Position counting
	// {{{

	always @(posedge i_clk)
	if (i_reset)
		f_posn <= 0;
	else if (M_CON_VALID && M_CON_READY)
	begin
		f_posn <= f_posn + 1;
		if (M_CON_LAST)
			f_posn <= 0;
	end

	always @(posedge i_clk)
	if (!M_CON_VALID)
		assert(f_posn == 0);
	else
		assert(f_posn < MAXPKTLN);

	always @(*)
	if (f_past_valid && M_CON_VALID)
		assert(no_space == (space_available == 0));

	always @(*)
	if (f_past_valid && M_CON_VALID)
	case(m_fsm)
	FSM_IDLE: begin
		assert(f_posn == 0);
		assert(m_data == 8'h00);
		assert(!m_dlast);
		assert(!m_last);
		end
	1: begin
		assert(f_posn == 1);
		assert(m_data == rdposn[23:16]);
		assert(!m_dlast);
		assert(!m_last);
		assert(rdptr == rdstart[LGFIFO-1:0]);
		end
	2: begin
		assert(f_posn == 2);
		assert(m_data == rdposn[15:8]);
		assert(!m_last);
		if (wrposn == 0)
			assert(m_dlast);
		if (rdposn != 0)
			assert(!m_dlast);
		assert(rdptr == rdstart);
		end
	3: begin
		assert(f_posn == 3);
		assert(m_data == rdposn[7:0]);
		if (wrposn == 0)
			assert(m_last);
		if (wrposn == 1)
			assert(m_dlast);
		if (rdposn != 0)
			assert(!m_last);
		assert(rdptr == rdstart+1);
		assert(r_data == mem[rdstart]);
		end
	4: begin
		assert(f_posn >= 4);
		assert(f_dptr + 2 == rdptr);
		end
	default: assert(0);
	endcase else if (f_past_valid && !M_CON_VALID)
	begin
		assert(m_fsm == FSM_IDLE);
		assert(f_posn == 0);
	end
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Contract (data) property
	// {{{

	// always @(*) assume(fc_posn >= 4);
	//
	// always @(*)
	// if (M_CON_VALID && f_posn == fc_posn)
	//	assert(M_CON_DATA == fc_data);
	//

	// }}}
`endif
// }}}
endmodule
