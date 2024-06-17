////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/ipheader.v
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
module	ipheader #(
		// {{{
		parameter	[15:0]	IPv4_PROTO = 16'h0800,	// IPv4
		parameter	[7:0]	SUB_PROTO  = 8'd17	// UDP
		// }}}
	) (
		input	wire	S_AXI_ACLK, S_AXI_ARESETN,
		// {{{
		// input wire	[47:0]	i_enet_src,
		input	wire	[47:0]	i_enet_dest,
		input	wire	[31:0]	i_ip_src,
		input	wire	[31:0]	i_ip_dest,
		// }}}
		// AXI Stream master port
		// {{{
		output	reg		M_AXI_TVALID,
		input	wire		M_AXI_TREADY,
		output	wire	[31:0]	M_AXI_TDATA,
		output	reg		M_AXI_TLAST
		// }}}
	);

	// Local declarations
	// {{{
	wire	[(6+2)*8-1:0]	enet_header;
	wire	[(5*4)*8-1:0]	ipv4_header;
	reg	[7*32-1:0]	shift_reg;
	reg	[2:0]		count;

	reg	valid_ipaddr, valid_macaddr;
	reg	[15:0]		pkt_id;
	// }}}

	// Ethernet header
	// {{{
	// Nominally, consists of a destination, source, and ethertype for
	//	IPv4
	// assign	enet_header = { i_enet_dest, i_enet_src, IPv4_PROTO };
	//

	// In our case, however, the network handler quietly inserts our
	// ethernet source into the ethernet header, so we don't need to
	// insert it again here--we can just insert the destination.
	assign	enet_header = { i_enet_dest, IPv4_PROTO };
	// }}}

	// IP v4 Header
	// {{{
	// We need to get the IP source and destination from somehwere.  For
	// now, we'll just punt and say those are defind externally.
	// The SUB_PROTO can (easily) be overwritten by the packet generator.
	//
	assign	ipv4_header = { 8'h45, 24'h00, // Zero length is a placeholder
				pkt_id,	// Packet "ID"
				16'h00,	// Fragmentation flags & offset
				// Zero checksum is a placeholder as well
				8'h80, SUB_PROTO, 16'h00,
				i_ip_src,
				i_ip_dest
				};
	// }}}

	// pkt_id
	// {{{
	// Use an LRS to generate a unique, but somewhat randomized, packet
	// ID
	localparam	[15:0]	IDFILL = 16'ha94b;

	initial	pkt_id = 1;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		pkt_id <= 1;
	else if (M_AXI_TVALID && M_AXI_TREADY && M_AXI_TLAST)
		pkt_id <= (pkt_id >> 1) ^ (pkt_id[0] ? IDFILL : 16'h0);
	// }}}

	// M_AXI_TVALID
	// {{{
`ifdef	VERILATOR
	always @(*)
		valid_macaddr = 1;
	always @(*)
		valid_ipaddr  = 1;
`else
	always @(posedge S_AXI_ACLK)
		valid_macaddr <= (i_enet_dest != 0);
	always @(posedge S_AXI_ACLK)
		valid_ipaddr <= (i_ip_dest != 0);
`endif

	initial	M_AXI_TVALID = 1'b0;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN)
		M_AXI_TVALID <= 1'b0;
	else if (M_AXI_TVALID && M_AXI_TREADY && M_AXI_TLAST)
		M_AXI_TVALID <= 1'b0;
	else if (!M_AXI_TVALID || (M_AXI_TREADY && M_AXI_TLAST))
		M_AXI_TVALID <= 1'b1; // valid_ipaddr && valid_macaddr;
	// }}}

	// shift_reg, M_AXI_TDATA
	// {{{
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !M_AXI_TVALID
			|| (M_AXI_TREADY && M_AXI_TLAST))
	begin
		shift_reg <= { enet_header, ipv4_header };
	end else if (M_AXI_TVALID && M_AXI_TREADY)
		shift_reg <= { shift_reg[6*32-1:0], 32'h0 };

	assign	M_AXI_TDATA = shift_reg[6*32 +: 32];
	// }}}

	// count, M_AXI_TLAST
	// {{{
	initial	count = 6;
	always @(posedge S_AXI_ACLK)
	if (!S_AXI_ARESETN || !M_AXI_TVALID || (M_AXI_TREADY && M_AXI_TLAST))
	begin
		count <= 6;
		M_AXI_TLAST <= 1'b0;
	end else if (M_AXI_TVALID && M_AXI_TREADY)
	begin
		count <= count - 1;
		M_AXI_TLAST <= (count == 1);
	end
	// }}}

	// Keep Verilator happy
	// {{{
	wire	unused;
	assign	unused = &{ 1'b0, valid_ipaddr, valid_macaddr };
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
	(* anyconst *)	reg [31:0]	f_src_ipaddr, f_dst_ipaddr;
	(* anyconst *)	reg [47:0]	f_mac_addr;
	wire	[2:0]	hdr_words;
	wire	[12:0]	hdr_packets;

	initial	f_past_valid = 0;
	always @(posedge S_AXI_ACLK)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(!S_AXI_ARESETN);

	// Incoming parameters must be constant
	// {{{
	always @(*)
	begin
		assume(i_enet_dest == f_mac_addr);
		assume(i_ip_src    == f_src_ipaddr);
		assume(i_ip_dest   == f_dst_ipaddr);
	end
	// }}}

	// AXI stream contract
	// {{{
	faxin_master #(
		.DATA_WIDTH(32), .MIN_LENGTH(7), .MAX_LENGTH(7)
	) faxin (
		// {{{
		.S_AXI_ACLK(S_AXI_ACLK), .S_AXI_ARESETN(S_AXI_ARESETN),
		.S_AXIN_VALID(M_AXI_TVALID),
		.S_AXIN_READY(M_AXI_TREADY),
		.S_AXIN_DATA(M_AXI_TDATA),
		.S_AXIN_LAST(M_AXI_TLAST),
		.S_AXIN_ABORT(1'b0),
		.f_stream_word(hdr_words),
		.f_packets_rcvd(hdr_packets)
		// }}}
	);

	always @(posedge S_AXI_ACLK)
	if (!f_past_valid || $past(!S_AXI_ARESETN))
		assert(!M_AXI_TVALID);
	else if ($past(M_AXI_TVALID && !M_AXI_TREADY))
	begin
		assert(M_AXI_TVALID);
		assert($stable(M_AXI_TDATA));
		assert($stable(M_AXI_TLAST));
	end

	always @(*)
	if (S_AXI_ARESETN && M_AXI_TVALID)
		assert(count == 6-hdr_words);
	// }}}

	// TLAST
	// {{{
	always @(posedge S_AXI_ACLK)
	if (M_AXI_TVALID)
		assert(M_AXI_TLAST == (count == 0));
	// }}}

	// count
	// {{{
	always @(*)
	if (S_AXI_ARESETN)
		assert(count <= 3'h6);
	// }}}

	// The contract for data out
	// {{{
	always @(*)
	if (M_AXI_TVALID)
	case(count)
	6: assert(M_AXI_TDATA == enet_header[63:32]);
	5: assert(M_AXI_TDATA == enet_header[31: 0]);
	4: assert(M_AXI_TDATA == ipv4_header[160-1:128]);
	3: assert(M_AXI_TDATA == ipv4_header[127:96]);
	2: assert(M_AXI_TDATA == ipv4_header[95:64]);
	1: assert(M_AXI_TDATA == ipv4_header[63:32]);
	0: assert(M_AXI_TDATA == ipv4_header[31:0]);
	default: assert(0);
	endcase
	// }}}

	// Induction property to pass the data out
	// {{{
	always @(*)
	if (M_AXI_TVALID)
	case(count)
	6: assert(shift_reg == { enet_header, ipv4_header });
	5: assert(shift_reg == { enet_header[31:0], ipv4_header, 32'h0 });
	4: assert(shift_reg == { ipv4_header, 64'h0 });
	3: assert(shift_reg == { ipv4_header[127:0], 96'h0 });
	2: assert(shift_reg == { ipv4_header[95:0], 128'h0 });
	1: assert(shift_reg == { ipv4_header[63:0], 160'h0 });
	0: assert(shift_reg == { ipv4_header[31:0], 192'h0 });
	default: assert(0);
	endcase
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Cover properties
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	always @(posedge S_AXI_ACLK)
		cover(S_AXI_ARESETN && M_AXI_TVALID && M_AXI_TREADY && M_AXI_TLAST);
	// }}}
`endif
// }}}
endmodule
