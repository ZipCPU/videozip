////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/ipmatch.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Matches (or not) packets for our IP address only.
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
`default_nettype none
// }}}
module	ipmatch (
		// {{{
		input	wire		i_clk, i_reset,
		//
		input	wire	[31:0]	i_ipaddr,
		//
		input	wire		S_AXIN_VALID,
		// output wire		S_AXIN_READY,	// Must be always ready
		input	wire	[7:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		output	reg		o_no_match
		// }}}
	);

	reg	[4:0]	addr;
	reg		is_ip, ipaddr_match;

	always @(posedge i_clk)
	if (i_reset)
	begin
		// {{{
		addr       <= 0;
		is_ip      <= 0;
		ipaddr_match <= 0;
		o_no_match <= 0;
		// }}}
	end else if (S_AXIN_ABORT || (S_AXIN_VALID && S_AXIN_LAST))
	begin
		// {{{
		addr       <= 0;
		is_ip      <= 0;
		ipaddr_match <= 0;
		o_no_match <= 0;
		// }}}
	end else if (S_AXIN_VALID)
	begin
		// {{{
		if (!addr[4])
			addr <= addr + 1;

		case(addr)
		6: is_ip <= (S_AXIN_DATA == 8'h08);
		7: is_ip <= is_ip && (S_AXIN_DATA == 8'h00);
		8: is_ip <= is_ip && (S_AXIN_DATA[7:4] == 4'h4);
		24: ipaddr_match <= (S_AXIN_DATA == i_ipaddr[31:24]);
		25: ipaddr_match <= ipaddr_match && (S_AXIN_DATA == i_ipaddr[23:16]);
		26: ipaddr_match <= ipaddr_match && (S_AXIN_DATA == i_ipaddr[15: 8]);
		27: ipaddr_match <= ipaddr_match && (S_AXIN_DATA == i_ipaddr[ 7: 0]);
		28: o_no_match <= !is_ip && !ipaddr_match;
		endcase
		// }}}
	end

endmodule
