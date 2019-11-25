////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbmouse.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Provide access, over the WB bus, to mouse information to
//		determine the location of the pointer on the screen or even on
//	a fictitious tableau.
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
`default_nettype	none
//
module	wbmouse(i_clk,
		// Wishbone accesses, read only interface ... saving
		//	that any writes will reset the mouse interface
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
		o_wb_stall, o_wb_ack, o_wb_data, 
		// Actual mouse interface
		i_ps2, o_ps2,
		// Interface to other things on the board
		o_scrn_mouse, // Mouse mapped to screen coordinates
		o_interrupt); // Mouse Button pressed
	input	wire		i_clk;
	// Wishbone interface
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[1:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	output	wire		o_wb_stall;
	output	reg		o_wb_ack;
	output	reg	[31:0]	o_wb_data;
	// Mouse interface
	input	wire	[1:0]	i_ps2;
	output	wire	[1:0]	o_ps2;
	// Other component interface
	output	wire	[31:0]	o_scrn_mouse;
	output	reg		o_interrupt;
	

	wire		m_stb;
	wire	[23:0]	m_data;
	wire	[6:0]	m_state;
	wire	[1:0]	m_errs;
	wire	[31:0]	ll_dbg;
	llmouse	driver(i_clk,
		(i_wb_stb)&&(i_wb_we)&&(i_wb_addr == 2'b01),
		i_ps2, o_ps2, m_stb, m_data, m_state, m_errs, ll_dbg);

	reg	[11:0]	m_xrows, m_ylines;
	always @(posedge i_clk)
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr == 2'b11))
		begin
			m_xrows  <= i_wb_data[27:16];
			m_ylines <= i_wb_data[11: 0];
		end

	wire		lftbtn, rhtbtn;
	assign	lftbtn = m_data[16];
	assign	rhtbtn = m_data[17];

	wire	[9:0]	x_data, y_data;
	assign	x_data = { m_data[20], m_data[22], m_data[15:8] };
	assign	y_data = { m_data[21], m_data[23], m_data[ 7:0] };

	reg	dir;
	always @(posedge i_clk)
		if (m_stb)
			dir <= (lftbtn)? 1'b0: (rhtbtn) ? 1'b1 : dir;

	// Now for tracking the Mouse for VGA purposes
	wire	[11:0]	w_scrnx;
	wire	[11:0]	w_scrny;
	mouseacc	#(12)	scrnxi(i_clk, m_xrows,  m_stb, x_data,w_scrnx);
	mouseacc	#(12)	scrnyi(i_clk, m_ylines, m_stb, y_data,w_scrny);

	assign	o_scrn_mouse = { lftbtn, rhtbtn, 2'h0, w_scrnx, 4'h0, w_scrny };

	// And let's make for one more result to report to the bus
	wire	[11:0]	w_busx, w_busy;
	wire	[31:0]	w_bus_mouse;
	mouseacc	#(12) busxacc(i_clk, 12'h3ff, m_stb, x_data, w_busx);
	mouseacc	#(12) busyacc(i_clk, 12'h3ff, m_stb, y_data, w_busy);
	assign w_bus_mouse = { lftbtn, rhtbtn, 2'h0, w_busx, 4'h0, w_busy };

	reg	[31:0]	raw_mouse;
	always @(posedge i_clk)
		raw_mouse <= { m_stb, m_state, m_data };

	always @(posedge i_clk)
		case(i_wb_addr)
		2'b00: o_wb_data <= w_bus_mouse;
		2'b01: o_wb_data <= raw_mouse;
		2'b10: o_wb_data <= o_scrn_mouse;
		2'b11: o_wb_data <= {4'h0, m_xrows, 4'h0, m_ylines };
		endcase

	initial	o_wb_ack = 1'b0;
	always @(posedge i_clk)
		o_wb_ack <= i_wb_stb;
	assign	o_wb_stall = 1'b0;

	// Now, let's do the interrupt
	reg	[1:0]	btnstate;
	always @(posedge i_clk)
		if (m_stb)
			btnstate <= { lftbtn, rhtbtn };
	always @(posedge i_clk)
		o_interrupt <= ((m_stb)&&(|( {lftbtn,rhtbtn} & (~btnstate) )));

	// Make verilator happy
	// verilator lint_off UNUSED
	wire	[42:0]	unused;
	assign	unused = { i_wb_cyc, m_errs, ll_dbg, i_wb_data[31:28], i_wb_data[15:12] };
	// verilator lint_on  UNUSED
endmodule
