////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	lloled.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is a low-level SPI output (not input) controller
//		designed to command interactions between an upper level
//	controller and a PModOLEDrgb.  As a result, this is a one-bit
//	(traditional, not quad) SPI controller, it has no MISO input bits,
//	and it also controls a DCN bits (output data at active high, vs
//	output control at active low).
//
//	This particular implementation was taken from a low-level QSPI
//	controller.  For those who wish to compare, the low-level QSPI
//	controller is very similar to the low-level EQSPI controller that is
//	also a part of the OpenArty project.
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
`define	OLED_IDLE	3'h0
`define	OLED_START	3'h1
`define	OLED_BITS	3'h2
`define	OLED_READY	3'h3
`define	OLED_STOP	3'h4
`define	OLED_STOP_B	3'h5
`define	OLED_STOP_C	3'h6

// Modes
`define	OLED_MOD_SPI	2'b00
`define	OLED_MOD_QOUT	2'b10
`define	OLED_MOD_QIN	2'b11

module	lloled(i_clk,
		// Module interface
		i_wr, i_dbit, i_word, i_len, o_busy,
		// OLED interface
		o_sck, o_mosi, o_dbit);
	parameter	CTRBITS = 8;
	input	wire		i_clk;
	// Chip interface
	//	Can send info
	//		i_wr = 1,
	//			i_word = { 1'b0, 32'info to send },
	//			i_len = # of bytes in word-1
	input	wire		i_wr, i_dbit;
	input	wire	[31:0]	i_word;
	input	wire	[1:0]	i_len;	// 0=>8bits, 1=>16 bits, 2=>24 bits, 3=>32 bits
	output	reg		o_busy;
	// Interface with the OLED lines
	output	reg		o_sck, o_mosi, o_dbit;

	reg	[5:0]	spi_len;
	reg	[31:0]	r_word;
	reg	[2:0]	state;
	initial	state = `OLED_IDLE;
	initial	o_sck   = 1'b1;
	initial	o_mosi  = 1'b0;
	initial	o_busy  = 1'b0;

	reg	[(CTRBITS-1):0]	counter;
	reg	last_counter, pre_last_counter;
	always @(posedge i_clk) // Clock cycle time > 150 ns > 300 ticks
		last_counter <= (counter == {{(CTRBITS-1){1'b0}},1'b1});
	always @(posedge i_clk)
		pre_last_counter <= (counter == {{(CTRBITS-2){1'b0}},2'b10});
	always @(posedge i_clk)
		if (state == `OLED_IDLE)
			counter <= {(CTRBITS){1'b1}};
		else
			counter <= counter + {(CTRBITS){1'b1}};
	always @(posedge i_clk)
		if ((state == `OLED_IDLE)&&(o_sck))
		begin
			o_busy  <= 1'b0;
			r_word <= i_word;
			spi_len<= { 1'b0, i_len, 3'b000 } + 6'h8;
			o_sck <= 1'b1;
			o_dbit <= i_dbit;
			if (i_wr)
			begin
				state <= `OLED_START;
				o_busy <= 1'b1;
			end
		end else if (state == `OLED_START)
		begin // We come in here with sck high, stay here 'til sck is low
			o_sck <= 1'b0;
			if (o_sck == 1'b0)
			begin
				state <= `OLED_BITS;
				spi_len<= spi_len - 6'h1;
				r_word <= { r_word[30:0], 1'b0 };
			end
			o_busy <= 1'b1;
			o_mosi <= r_word[31];
		end else if (~last_counter)
		begin
			o_busy <= (!pre_last_counter)||(!o_sck)
				||(state != `OLED_READY)||(~i_wr);
		end else if (~o_sck)
		begin
			o_sck <= 1'b1;
			o_busy <= 1'b1;
		end else if (state == `OLED_BITS)
		begin
			// Should enter into here with at least a spi_len
			// of one, perhaps more
			o_sck <= 1'b0;
			o_busy <= 1'b1;
			o_mosi <= r_word[31];
			r_word <= { r_word[30:0], 1'b0 };
			spi_len <= spi_len - 6'h1;
			if (spi_len == 6'h1)
				state <= `OLED_READY;
		end else if (state == `OLED_READY)
		begin
			o_busy <= 1'b1;
			// This is the state on the last clock (both low and
			// high clocks) of the data.  Data is valid during
			// this state.  Here we chose to either STOP or
			// continue and transmit more.
			o_sck <= 1'b0;
			if((~o_busy)&&(i_wr))// Acknowledge a new request
			begin
				state <= `OLED_BITS;
				o_busy <= 1'b1;
				o_sck <= 1'b0;

				// Set up the first bits on the bus
				o_mosi <= i_word[31];
				r_word <= { i_word[30:0], 1'b0 };
				spi_len<= { 1'b0, i_len, 3'b111 };

				// Read a bit upon any transition
			end else begin
				o_sck <= 1'b1;
				state <= `OLED_STOP;
				o_busy <= 1'b1;
			end
		end else if (state == `OLED_STOP)
		begin
			o_sck   <= 1'b1; // Stop the clock
			o_busy  <= 1'b1; // Still busy till port is clear
			state <= `OLED_STOP_B;
		end else if (state == `OLED_STOP_B)
		begin
			o_sck <= 1'b1;
			// Do I need this????
			// spi_len <= 3; // Minimum CS high time before next cmd
			state <= `OLED_STOP_C;
			o_mosi <= 1'b1;
			o_busy <= 1'b1;
		end else // if (state == `OLED_STOP_C)
		begin
			// Keep us in idle for at least a full clock period.
			o_sck <= 1'b1;
			// Do I need this????
			// spi_len <= 3; // Minimum CS high time before next cmd
			state <= `OLED_IDLE;
			o_mosi <= 1'b1;
			o_busy <= 1'b1;
		end
		/*
		*/

endmodule

