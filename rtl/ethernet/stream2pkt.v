////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/stream2pkt.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Converts an AXI stream back into a AXI packet stream.  Specific
//		to the AXI stream is the fact that the first word in the stream
//	specifies the number of bytes to be generated in the AXI packet stream.
//
//	The AXI network packet stream abort feature is unused.  Packets once
//	started are guaranteed to be completed.  They may not be completed in
//	a timely fashion, but they will be completed.
//
// PKT FORMAT:
//	Length word:			Specifies the length of the entire
//					packet in bytes, payload plus 4 byte
//					length word.  Minimum value, therefore,
//					is a length of 5.
//	(Length-1)/4 data words:	Describes the payload of the packet
//					Bytes are left justified, MSB first.
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
module	stream2pkt #(
		// {{{
		parameter	BW=8,	// Outgoing data width (one byte)
		// Incoming data (i.e. memory) width
		parameter	S_AXIS_DATA_WIDTH = 32,
		parameter	MAX_PACKET_SIZE = 2048,
		localparam	S_DW = S_AXIS_DATA_WIDTH,
		localparam	LSB = $clog2(S_AXIS_DATA_WIDTH/BW)
		// }}}
	) (
		// {{{
		input	wire		S_AXI_ACLK,
		input	wire		S_AXI_ARESETN,
		//
		// Incoming packets
		input	wire		S_AXIS_TVALID,
		output	wire		S_AXIS_TREADY,
		input	wire [S_DW-1:0]	S_AXIS_TDATA,
		//
		// Outgoing AXI stream
		output	reg		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	reg [BW-1:0]	M_AXIN_DATA,
		output	reg 		M_AXIN_LAST,
		output	wire 		M_AXIN_ABORT	// Always zero
		// }}}
	);

	// Register/net declarations
	// {{{
	localparam			S_IDLE = 1'b0, S_DATA = 1'b1;
	reg				state;

	wire				skd_ready, skd_valid;
	wire	[S_DW-1:0]		skd_data;

	wire				out_of_bounds;

	reg				pkt_abort;
	reg	[S_DW-BW-1:0]		pkt_data;
	reg	[$clog2(S_DW-BW)-1:0]	pkt_bytes;
	reg	[S_DW-1:0]		pkt_len;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skid buffer input, to help timing closure
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	skidbuffer #(
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1),
`endif
		.DW(S_DW)
	) skd (
		.i_clk(S_AXI_ACLK), .i_reset(!S_AXI_ARESETN),
		.i_valid(S_AXIS_TVALID), .o_ready(S_AXIS_TREADY),
			.i_data(S_AXIS_TDATA),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data(skd_data)
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// State machine processing, and data unwrapping
	// {{{
	initial	state      = S_IDLE;
	initial	pkt_abort  = 1'b0;
	initial	pkt_len    = 0;		// Bytes remaining in the packet
	initial	pkt_bytes  = 0;
	initial	M_AXIN_LAST   = 0;
	initial	M_AXIN_VALID  = 0;

	generate if (S_DW > 16)
	begin : GEN_SKD_OOB
		assign	out_of_bounds = (skd_data[S_DW-1:16] != 0);
	end else begin : NO_OOB
		assign	out_of_bounds = 0;
	end endgenerate

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
	begin
		// {{{
		state <= S_IDLE;
		pkt_abort <= 0;
		pkt_len   <= 0;
		pkt_bytes <= 0;
		M_AXIN_LAST  <= 0;
		M_AXIN_VALID <= 0;
		// }}}
	end else case(state)
	S_IDLE: begin
		// {{{
		pkt_len   <= 0;
		pkt_bytes <= 0;			// Bytes loaded in current word
		pkt_abort <= 0;
		M_AXIN_LAST  <= 0;
		M_AXIN_VALID <= 0;
		if (skd_valid && skd_ready)
		begin
			if (!out_of_bounds && skd_data > (1<<LSB))
			begin
				pkt_len  <= skd_data-(1<<LSB);	// Bytes remaining n pkt
				state     <= S_DATA;
				pkt_abort <= (skd_data >= MAX_PACKET_SIZE);
			end
		end end
		// }}}
	S_DATA: begin
		// {{{
			// M_AXIN_LAST
			// {{{
			if (!M_AXIN_VALID || M_AXIN_READY)
				M_AXIN_LAST <= !pkt_abort && (pkt_len <= 1 + (M_AXIN_VALID ? 1:0)) && (pkt_bytes>0 || skd_valid);
			// }}}

			// state, pkt_len
			// {{{
			if (pkt_abort)
			begin
				if (skd_valid && skd_ready)
				begin
					if (pkt_len > (1<<LSB))
						pkt_len <= pkt_len - (1<<LSB);
					else begin
						pkt_len <= 0;
						state <= S_IDLE;
					end
				end
			end else if (M_AXIN_VALID && M_AXIN_READY)
			begin
				if (pkt_len > 0)
					pkt_len <= pkt_len - 1;

				if (pkt_len <= 1)
					state <= S_IDLE;
			end
			// }}}

			if (skd_valid && skd_ready)
			begin
				// M_AXIN_[VALID|DATA], pkt_data
				// {{{
				M_AXIN_VALID <= !pkt_abort;
				M_AXIN_DATA  <= skd_data[S_DW-1:S_DW-BW];

				pkt_data <= skd_data[S_DW-BW-1:0];

				// Verilator lint_off WIDTH
				if (pkt_len - (M_AXIN_VALID ? 1:0) < S_DW/8)
				begin
					pkt_bytes <= 0;
					if (pkt_len + (M_AXIN_VALID ? 1:0)>= 2)
						// pkt_bytes <= pkt_len-2;
						pkt_bytes <= pkt_len - (M_AXIN_VALID ? 1:0) - 1;
				end else
					pkt_bytes <= S_DW / 8 - 1;
				// Verilator lint_on  WIDTH
				// }}}
			end else if (pkt_abort ||(M_AXIN_VALID && M_AXIN_READY))
			begin
				M_AXIN_DATA <= pkt_data[S_DW-BW-1:S_DW-2*BW];
				pkt_data <= { pkt_data[S_DW-2*BW-1:0],
								{(BW){1'b0}} };

				M_AXIN_VALID <= !pkt_abort && (pkt_bytes > 0);//&& !M_AXIN_LAST;

				if (pkt_bytes > 0)
					pkt_bytes <= pkt_bytes - 1;
			end

			if (pkt_abort)
				pkt_bytes <= 0;
		end
		// }}}
	endcase

	assign	M_AXIN_ABORT = 1'b0;

	assign	skd_ready = (!M_AXIN_VALID || M_AXIN_READY)
				&&(state == S_IDLE || !M_AXIN_LAST || pkt_abort)
				&&(pkt_bytes == 0);
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
	reg	f_past_valid;
	reg	[15:0]	s_word, fpkt_len, m_word;

	initial	f_past_valid = 1'b0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1'b1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	////////////////////////////////////////////////////////////////////////
	//
	// Interface properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assume(!S_AXIS_TVALID);
	else if ($past(S_AXIS_TVALID && !S_AXIS_TREADY))
	begin
		assume(S_AXIS_TVALID);
		assume($stable(S_AXIS_TDATA));
	end

	////////////////////////////////////////////////////////////////////////
	//
	// Slave word counting
	// {{{
	reg	[15:0]	ftotal_words, frounded_words;

	always @(*)
		frounded_words = fpkt_len + (1<<LSB)-1;
	always @(*)
		ftotal_words = frounded_words >> LSB;

	initial	s_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		s_word <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY)
	begin
		s_word <= s_word + 1;

		if (s_word == 0 && S_AXIS_TDATA < 5)
			s_word <= 0;
		if (s_word > 0 && (s_word + 1 >= ftotal_words))
			s_word <= 0;
	end

	initial	fpkt_len = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		fpkt_len <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && s_word == 0)
	begin
		if (S_AXIS_TDATA > 4)
			fpkt_len <= S_AXIS_TDATA;
	end

	always @(*)
	if (S_AXIS_TVALID && s_word == 0)
		assume(S_AXIS_TDATA <= 4095);

	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
		assert(fpkt_len >= 5 && fpkt_len <= 4095);

	always @(*)
	if (fpkt_len == 0)
		assert(s_word == 0);

	// Packet length of 12		13	14	15	16	17
	//	s_word = 0		 0	 0	 0	 0	 0
	//		1		 1	 1	 1	 1	 1
	//		2		 2	 2	 2	 2	 2
	//		0		 3	 3	 3	 3	 3
	//				 0	 0	 0	 0	 4
	//								 0
	//
	always @(*)
	if (S_AXI_ARESETN && fpkt_len > 0)
		assert(s_word < ftotal_words);

	always @(*)
	if (S_AXI_ARESETN && state == S_IDLE)
		assert(s_word == 0);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Master (outgoing) word counting
	// {{{
	initial	m_word = 0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		m_word <= 0;
	else if (M_AXIN_VALID && M_AXIN_READY)
	begin
		m_word <= m_word + 1;

		if (M_AXIN_LAST)
			m_word <= 0;
	end
	// }}}

	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
	begin
		assert(pkt_len >= (M_AXIN_VALID ? 1:0) + pkt_bytes);

		assert(pkt_len + (1<<LSB) <= fpkt_len);

		if (pkt_abort)
		begin
			if (pkt_len <  (1<<LSB) && pkt_abort)
			begin
				assert(s_word +1 == ftotal_words);
			end else begin
				assert(s_word + pkt_len[15:LSB]
				+ ((|pkt_len[LSB-1:0]) ? 1:0) == ftotal_words);
			end

			assert(fpkt_len[LSB-1:0] == pkt_len[LSB-1:0]);
		end else if (pkt_len == (M_AXIN_VALID ? 1:0) + pkt_bytes)
		begin
			assert(s_word == 0);
		end else
			assert((s_word << LSB)
				+ pkt_len - (M_AXIN_VALID ? 1:0) - pkt_bytes
					== fpkt_len);
	end


	always @(*)
	if (S_AXI_ARESETN && state != S_IDLE)
	begin
		if (pkt_abort)
		begin
			assert(m_word == 0);
		end else if (s_word != 0)
		begin
			assert((1<<LSB) + m_word + pkt_bytes + (M_AXIN_VALID ? 1:0) == (s_word << LSB));
		end else
			assert(pkt_len <= (1<<LSB));
	end

	always @(*)
	if (S_AXI_ARESETN && state == S_IDLE)
	begin
		assert(m_word == 0);
		assert(pkt_bytes == 0);
	end

	always @(*)
	if (S_AXI_ARESETN && state == S_DATA)
	begin
		assert(pkt_len < 4092);
		if (pkt_bytes != 0)
			assert(M_AXIN_VALID);
		if (pkt_abort)
			assert(pkt_bytes == 0);
	end

	always @(*)
	if (S_AXI_ARESETN && !pkt_abort && (state == S_DATA))
		assert(M_AXIN_LAST == (M_AXIN_VALID && pkt_len == 1));

	always @(posedge S_AXI_ACLK)
	if (S_AXI_ARESETN && $past(S_AXI_ARESETN) && $past(state == S_DATA))
	begin
		if ($past(pkt_abort))
		begin
			assert(state == ((pkt_len == 0) ? S_IDLE : S_DATA));
		end else if(!$past(M_AXIN_VALID && M_AXIN_READY && M_AXIN_LAST))
			assert(state == S_DATA);
	end

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || !$past(S_AXI_ARESETN))
		assert(!M_AXIN_VALID);
	else if ($past(M_AXIN_VALID && !M_AXIN_READY))
	begin
		assert(M_AXIN_VALID);
		assert($stable(M_AXIN_DATA));
	end

	always @(*)
	if (pkt_abort)
	begin
		assert(!M_AXIN_VALID);
	end else if (M_AXIN_VALID)
	begin
		assert(pkt_len > 0);
		// assert(M_AXIN_VALID == ((pkt_len > 0)&&(pkt_bytes > 0)));
	end else if (pkt_bytes > 0)
		assert(M_AXIN_VALID);

	always @(*)
	if (M_AXIN_VALID || state == S_DATA)
		assert(pkt_bytes +1 <= pkt_len);

	always @(*)
	if (state == S_IDLE)
		assert(pkt_len == 0);

	always @(*)
		assert(pkt_bytes <= S_DW/8-1);
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	reg	[15:0]	cvr_stuck_cycles;

	reg	[2:0]	cvr_packets;

	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		cvr_packets <= 0;
	else if (S_AXIS_TVALID && S_AXIS_TREADY && state == S_IDLE
			&& S_AXIS_TDATA > 9 && !cvr_packets[2])
		cvr_packets <= cvr_packets + 1;

	always @(*)
	if (S_AXI_ARESETN)
		cover(cvr_packets == 2'b10 && !M_AXIN_VALID && state == S_IDLE);

	always @(posedge S_AXI_ACLK)
	begin
		cvr_stuck_cycles <= cvr_stuck_cycles + 1;
		if (!S_AXI_ARESETN || !S_AXIS_TVALID || S_AXIS_TREADY
				|| M_AXIN_VALID || M_AXIN_READY)
			cvr_stuck_cycles <= 0;

		cover(f_past_valid && cvr_stuck_cycles > 30);


		if (f_past_valid)
			assert(cvr_stuck_cycles < 10);
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Simplifying assumptions
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	// No simplifying assumptions

	// }}}

	// Make Verilator happy
	// {{{
	// Verilator lint_off UNUSED
	wire	unused_formal;
	assign	unused_formal = &{ 1'b0 };
	// Verilator lint_on  UNUSED
	// }}}
`endif // FORMAL
// }}}
endmodule
