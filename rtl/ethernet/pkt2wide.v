////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/ethernet/pkt2wide.v
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Convert a network data stream from 8-bits per clock at 125MHz
//		to 32-bits per clock at 32MHz or above.  Format is AXIN stream,
//	that is--AXI streams with aborts.
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
module	pkt2wide #(
		parameter [0:0]	OPT_LITTLE_ENDIAN = 0,
		parameter	OW = 32
	) (
		// {{{
		input	wire		S_AXI_ACLK, S_AXI_ARESETN,
		input	wire		i_net_clk, i_net_reset_n,
		//
		input	wire		S_AXIN_VALID,
		output	wire		S_AXIN_READY,
		input	wire	[7:0]	S_AXIN_DATA,
		input	wire		S_AXIN_LAST,
		input	wire		S_AXIN_ABORT,
		//
		output	wire		M_AXIN_VALID,
		input	wire		M_AXIN_READY,
		output	wire	[31:0]	M_AXIN_DATA,
		output	wire		M_AXIN_LAST,
		output	wire		M_AXIN_ABORT
		// }}}
	);

	// Local declarations
	// {{{
	reg [$clog2(OW/8)-1:0]	pre_fill;
	reg	[OW-8-1:0]	pre_wide;

	reg			n_write, n_active, n_last, n_abort;
	wire			n_full;
	reg	[OW-1:0]	n_wide;

	wire			afif_abort, afif_empty;
	// }}}

	////////////////////////////////////////////////////////////////////////
	//
	// Pack incoming data, OW (nominally 32) bits per word
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	assign	S_AXIN_READY = !n_write || !n_full;
			// || !(&pre_fill || S_AXIN_LAST || S_AXIN_READY);

	// pre_fill, pre_wide
	// {{{
	always @(posedge i_net_clk)
	if (!i_net_reset_n)
	begin
		pre_fill <= 0;
		pre_wide <= 0;
	end else if (S_AXIN_ABORT)
	begin
		pre_wide <= 0;
		pre_fill <= 0;
	end else if (S_AXIN_VALID && S_AXIN_READY)
	begin
		// This *only* works because S_AXIN_DATA has 8 bits
		if (OPT_LITTLE_ENDIAN)
			pre_wide <= { pre_wide[OW-17:0], S_AXIN_DATA };
		else
			pre_wide <= { S_AXIN_DATA, pre_wide[OW-8-1:8] };

		if (S_AXIN_LAST || &pre_fill)
		begin
			pre_fill <= 0;
			pre_wide <= 0;
		end else begin
			pre_fill <= pre_fill + 1;
		end
	end
	// }}}

	// n_write, n_active, n_wide, n_last, n_abort
	// {{{
	always @(posedge i_net_clk)
	if (!i_net_reset_n)
	begin
		// {{{
		n_write  <= 0;
		n_active <= 0;
		n_wide   <= 0;
		n_last   <= 0;
		n_abort  <= 0;
		// }}}
	end else if (S_AXIN_ABORT && (!S_AXIN_VALID || S_AXIN_READY))
	begin
		// {{{
		n_write <= n_active;
		// n_active <= n_active;
		// n_wide <= don't care;
		n_abort <= n_active;
		n_last  <= n_active;
		// }}}
	end else if (S_AXIN_VALID && S_AXIN_READY && (&pre_fill || S_AXIN_LAST))
	begin
		// {{{
		n_write  <= 1'b1;
		n_active <= 1'b1;
		n_last   <= S_AXIN_LAST;
		n_abort  <= 1'b0;

		if (OPT_LITTLE_ENDIAN)
			n_wide <= { pre_wide, S_AXIN_DATA };
		else
			n_wide <= { S_AXIN_DATA, pre_wide };
		// }}}
	end else if (!n_full)
	begin
		// {{{
		n_write <= 0;
		n_last  <= 0;
		n_abort <= 0;
		if (n_last || n_abort)
			n_active <= 0;
		// }}}
	end
	// }}}

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Async FIFO to move to the S_AXI_ACLK domain
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//

	afifo #(
		.WIDTH(2+32)
	) u_afifo (
		// {{{
		.i_wclk(i_net_clk), .i_wr_reset_n(i_net_reset_n),
		.i_wr(n_write), .i_wr_data({ n_abort, n_last, n_wide }),
			.o_wr_full(n_full),
		.i_rclk(S_AXI_ACLK), .i_rd_reset_n(S_AXI_ARESETN),
		.i_rd(M_AXIN_READY),
		.o_rd_data({ afif_abort, M_AXIN_LAST, M_AXIN_DATA }),
		.o_rd_empty(afif_empty)
		// }}}
	);

	assign	M_AXIN_VALID = !afif_empty;
	assign	M_AXIN_ABORT = M_AXIN_VALID && afif_abort;
	// }}}
endmodule
