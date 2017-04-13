////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	llmouse.v
//
// Project:	Basys3 Demonstration Project
//
// Purpose:	This is the "Low Level" driver/controller for a PS/2 mouse,
//		using the USB HID protocol on the Basys3 board.
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2016, Gisselquist Technology, LLC
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
// with this program.  (It's in the $(ROOT)/doc directory, run make with no
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

`define	WBMS_TX_RESET		6'h00
`define	WBMS_PASSED_SELFTEST	6'h20
`define	WBMS_IS_MOUSE		6'h30
`define	WBMS_STREAM_MODE	6'h38
`define	WBMS_DATA_PROMISED	6'h3c
`define	WBMS_DATA_MODE		6'h3d
`define	WBMS_READ_X		6'h3e
`define	WBMS_READ_Y		6'h3f
module	llmouse(i_clk, i_rst, i_ps2, o_ps2, o_mouse_stb, o_mouse_data,
		o_mstate, o_errs, o_dbg);
	input	wire		i_clk, i_rst;
	input	wire	[1:0]	i_ps2;
	output	wire	[1:0]	o_ps2;
	output	reg		o_mouse_stb;
	output	wire	[23:0]	o_mouse_data;
	output	reg	[6:0]	o_mstate;
	output	wire	[1:0]	o_errs;
	output	wire	[31:0]	o_dbg;
	//

	// o_mstate[6:0]:
	//	1'b	Mouse has passed self-test
	//	1'b	Mouse has identified itself
	//	1'b	Mouse has gone to stream mode
	//	1'b	Mouse promises data
	//	1'b	Mouse is producing data
	//	1'b	Command given, no acknowledgement
	//
	reg		tx_stb;
	reg	[4:0]	r_tx_data;
	wire	ps2_ferr, ps2_perr, ps2_busy;
	wire	rx_stb;
	wire	[7:0]	rx_data;
	wire	[26:0]	ps2_dbg;
	wire	[7:0]	tx_data;
	assign	tx_data = { 3'b111, r_tx_data };
	llps2	ps2iface(i_clk, i_ps2, o_ps2, rx_stb, rx_data,
				tx_stb, tx_data, ps2_ferr, ps2_perr,
				ps2_busy, ps2_dbg);
	assign	o_errs = { ps2_ferr, ps2_perr };

	// Upon startup, 
	//	Mouse sends 8'haa (SELF_TEST_PASSED)
	//	Mouse sends 8'h00 (THIS IS A MOUSE)
	//	We send 8'hff (INSIST ON ANOTHER RESET, We'll do this on WB command)
	//		Mouse replies 8'haa (self-test passed)
	//		Mouse replies 8'h00 (this is a mouse)
	//	We send 8'hea (Enter stream mode)
	//		Mouse replies 8'hfa (Acknowledgement)
	//	We send 8'hf4 (Enable data reporting)
	//		Mouse replies 8'hfa (Acknowledgement)
	//	// computer-engineering.org/ps2mouse/ states that the mouse automatically goes into stream mode, but doesn't report
	//	Mouse sends data: Status, Xdir, Ydir


	// Run the transmitter
	reg	[7:0]	r_status, r_xmotion, r_ymotion;
	initial	o_mstate = 7'h00;
	always @(posedge i_clk)
	begin
		// o_mstate[8] <= ps2_ferr;
		// o_mstate[7] <= ps2_ferr;
		o_mouse_stb <= 1'b0;
		if (tx_stb)
			o_mstate[0] <= 1'b1;
		tx_stb <= (tx_stb)&&(ps2_busy); // Leave TX high until the controller acknowledges it
		if ((i_rst)||(ps2_ferr)) // Reset the interface on a write
		begin
			o_mstate <= { `WBMS_TX_RESET, 1'b0 };
			tx_stb <= 1'b1; // Issue a reset command to the device
			r_tx_data <= 5'h1f; // 8'hff; 
		end else if ((o_mstate[6:1] == `WBMS_TX_RESET)&&(rx_stb)&&(rx_data == 8'hAA))
			o_mstate <= { `WBMS_PASSED_SELFTEST, 1'b0 };
		else if ((o_mstate[6:1] == `WBMS_PASSED_SELFTEST)&&(rx_stb)&&(rx_data == 8'h00))
		begin
			o_mstate <= { `WBMS_IS_MOUSE, 1'b0 };
			tx_stb <= 1'b1;
			r_tx_data <= 5'h0a; // 8'hea; // Send us to stream mode
		end else if ((o_mstate[6:1] == `WBMS_IS_MOUSE)&&(rx_stb)&&(rx_data == 8'hfa))
		begin
			o_mstate <= { `WBMS_STREAM_MODE, 1'b0 };
			tx_stb <= 1'b1;
			r_tx_data <= 5'h14; // 8'hf4; // Request reporting
		end else if ((o_mstate[6:1] == `WBMS_STREAM_MODE)&&(rx_stb)&&(rx_data == 8'hfa))
			o_mstate <= { `WBMS_DATA_PROMISED, 1'b0 };
		else if (o_mstate[6:1] == `WBMS_DATA_PROMISED)
		begin
			if (rx_stb)
			begin
				r_status <= rx_data;
				o_mstate <= { `WBMS_READ_X, 1'b0 };
			end
		end else if (o_mstate[6:1] == `WBMS_DATA_MODE)
		begin
			if (rx_stb)
			begin
				r_status <= rx_data;
				o_mstate <= { `WBMS_READ_X, 1'b0 };
			end
		end else if (o_mstate[6:1] == `WBMS_READ_X)
		begin
			if (rx_stb)
			begin
				r_xmotion <= rx_data;
				o_mstate <= { `WBMS_READ_Y, 1'b0 };
			end
		end else if (o_mstate[6:1] == `WBMS_READ_Y)
		begin
			r_ymotion <= rx_data;
			if (rx_stb)
			begin
				o_mstate <= { `WBMS_DATA_MODE, 1'b0 };
				o_mouse_stb <= 1'b1;
			end
		end
	end

	assign	o_mouse_data = { r_status, r_xmotion, r_ymotion };

	assign	o_dbg = { o_mstate[6:2], ps2_dbg };

endmodule

