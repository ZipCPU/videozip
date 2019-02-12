////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	llps2.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
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
`define	PS_IDLE		4'h0
`define	PS_RX_START	4'h1
`define	PS_RX_DATA	4'h2
`define	PS_RX_PARITY	4'h3
`define	PS_RX_STOP	4'h4
`define	PS_RX_PREIDLE	4'h5
`define	PS_RX_ERR	4'h6
`define	PS_TX_RTS	4'h7
`define	PS_TX_START	4'h8
`define	PS_TX_DATA	4'h9
`define	PS_TX_PARITY	4'ha
`define	PS_TX_ACK	4'hb
`define	PS_TX_PREIDLE	4'hc
`define	PS_TX_STOP	4'hd
module	llps2(i_clk, i_ps2, o_ps2, o_rx_stb, o_rx_data,
			i_tx_stb, i_tx_data, o_frame_err, o_parity_err, o_busy,
			o_dbg);
	parameter	TICKS_PER_BIT=16'h2000,
				TICKS_PER_HALFBIT=TICKS_PER_BIT/2,
				TICKS_PER_QUARTERBIT=TICKS_PER_BIT/4,
				TICKS_PER_HUNDRED_USEC = 16'd10000;
	input	wire		i_clk;
	input	wire	[1:0]	i_ps2;
	output	reg	[1:0]	o_ps2;
	output	reg		o_rx_stb;
	output	reg	[7:0]	o_rx_data;
	input	wire		i_tx_stb;
	input	wire	[7:0]	i_tx_data;
	output	reg		o_frame_err, o_parity_err;
	output	reg		o_busy;
	output	wire	[26:0]	o_dbg;

	reg	[1:0]	q_ps2, qq_ps2, ck_ps2;
	wire		ck_clk, ck_dat, falling_edge;
	//
	// Always clock any unclocked inputs twice with the rising edge of the
	// incoming clock, so as to remove any problems with metastability.
	//
	always @(posedge i_clk)
	begin
		q_ps2 <= i_ps2;
		qq_ps2 <= q_ps2;
		ck_ps2 <= qq_ps2;
	end

	//
	// Notice that the Clock was i_ps2[1] and the data line was i_ps2[0].
	// Now that they've both been clocked twice, we create new clock and
	// data lines with the prefix "ck_" to note that they've now been
	// synchronized to our local clock.
	assign	ck_clk = ck_ps2[1];
	assign	ck_dat = ck_ps2[0];
	assign	falling_edge = (~ck_clk)&&(qq_ps2[1]);

	reg	[16:0]	idle_count;	// about 1.3 ms, or 13 bits at 10 kHz
	initial	idle_count = 17'h1ffff;
	always @(posedge i_clk)
	begin
		if ((&ck_ps2)&&(~(&idle_count)))
			idle_count <= idle_count + 1;
		else if (~(&ck_ps2))
			idle_count <= 0;
	end

	reg		parity;
	reg	[7:0]	data_reg;
	reg	[4:0]	data_len;
	reg	[3:0]	state;
	reg	[15:0]	counter;
	initial	state = `PS_RX_ERR;
	initial counter = 16'h00;
	initial	o_ps2   = 2'b11;
	always @(posedge i_clk)
	begin
		o_frame_err  <= 1'b0;
		o_parity_err <= 1'b0;
		o_rx_stb     <= 1'b0;
		if (state == `PS_IDLE)
		begin
			o_busy <= ~(&idle_count);
			o_ps2 <= 2'b11; // Turn off output via pullup resistors
			if (~ck_dat)
			begin // Go into receive mode, data must go low first
				counter <= TICKS_PER_QUARTERBIT;
				state <= `PS_RX_START;
				o_busy <= 1'b1;
			end else if ((i_tx_stb)&&(~o_busy))
			begin
				counter <= TICKS_PER_HUNDRED_USEC;
				state <= `PS_TX_RTS;
				o_ps2 <= 2'b00;
				data_reg <= i_tx_data;
				data_len <= 8;
				o_busy <= 1'b1;
			end
		end else if (counter > 0)
		begin
			counter <= counter - 1;
		end else if (state == `PS_TX_RTS)
		begin
			// Release the clock, hold data low
			o_ps2 <= 2'b10;
			counter <= TICKS_PER_QUARTERBIT;
			state <= `PS_TX_START;
		end else if (state == `PS_TX_START)
		begin // Device creates the clock, come in here with low data ln
			if (falling_edge)
			begin // Can we rescue this by grabbing the new value?
				state <= `PS_TX_DATA;
				counter <= TICKS_PER_QUARTERBIT;
				o_ps2 <= { 1'b1, data_reg[0] };
				data_reg <= { 1'b0, data_reg[7:1] };
				data_len <= data_len - 1;
				parity <= data_reg[0];
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_TX_DATA)
		begin
			if (falling_edge)
			begin
				counter <= TICKS_PER_QUARTERBIT;
				data_reg <= { 1'b0, data_reg[7:1] };
				data_len <= data_len - 1;
				if (data_len > 0)
				begin
					o_ps2 <= { 1'b1, data_reg[0] };
					parity <= parity ^ data_reg[0];
				end else begin
					o_ps2 <= { 1'b1, (parity)? 1'b0:1'b1 };
					state <= `PS_TX_PARITY;
				end
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_TX_PARITY)
		begin
			if (falling_edge)
			begin
				counter <= TICKS_PER_QUARTERBIT;
				o_ps2 <= 2'b11;
				state <= `PS_TX_ACK;
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		/*
		* But ... host->device doesn't have a stop bit, just an
		* acknowledge bit from the device
		end else if (state == `PS_TX_STOP)
		begin
			if (falling_edge)
			begin
				counter <= TICKS_PER_QUARTERBIT;
				o_ps2 <= 2'b11;
				state <= `PS_TX_ACK;
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		*/
		end else if (state == `PS_TX_ACK)
		begin
			if (falling_edge)
			begin
				o_frame_err <= ck_dat;
				state <= `PS_TX_PREIDLE;
				counter <= TICKS_PER_QUARTERBIT;
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_TX_PREIDLE)
		begin
			// No resetting of the counter here, we're just
			// headed to idle
			state <= `PS_IDLE;
			o_ps2 <= 2'b11;
		end else if (state == `PS_RX_START)
		begin
			o_ps2 <= 2'b11;
			if (falling_edge) // If the clock goes low
			begin
				state <= `PS_RX_DATA;
				data_reg <= 8'h00;
				data_len <= 5'h7;
				counter <= TICKS_PER_QUARTERBIT;
				parity <= 1'b0;
			end else if (&idle_count)
			begin // An error occurred, don't get stuck here ...
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_RX_DATA)
		begin
			o_ps2 <= 2'b11;
			if (falling_edge) // On falling edge of clk
			begin
				data_reg <= { ck_dat, data_reg[7:1] };
				data_len <= data_len - 1;
				counter <= TICKS_PER_HALFBIT;
				parity <= parity ^ ck_dat;
				if (data_len == 0)
				begin
					state <= `PS_RX_PARITY;
				end
			end else if (&idle_count)
			begin
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_RX_PARITY)
		begin
			o_ps2 <= 2'b11;
			if (falling_edge) // On falling clock edge
			begin
				if ((parity ^ ck_dat)==1'b1)
				begin
					o_rx_stb <= 1'b1;
					o_rx_data <= data_reg;
					state <= `PS_RX_STOP;
				end else begin
					state <= `PS_RX_ERR;
					o_parity_err <= 1'b1;
				end
				counter<= TICKS_PER_HALFBIT;
			end else if (&idle_count)
			begin
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_RX_STOP)
		begin
			o_ps2 <= 2'b11;
			if (falling_edge)
			begin
				counter <= TICKS_PER_HALFBIT;
				state <= `PS_RX_PREIDLE;
			end else if (&idle_count)
			begin
				o_frame_err <= 1'b1;
				state <= `PS_RX_ERR;
			end
		end else if (state == `PS_RX_PREIDLE)
		begin
			// No resetting of the counter here, we're just
			// headed to idle
			state <= `PS_IDLE;
			o_busy <= 1'b1;
			o_ps2 <= 2'b11;
		end else // if (state == `PS_RX_ERR)
		begin
			if (&idle_count)
				state <= `PS_IDLE;
			o_ps2 <= 2'b11;
			o_busy <= 1'b1;
			o_ps2 <= 2'b11;
		end
	end

	assign o_dbg = { i_tx_stb, i_tx_data, o_rx_data, o_rx_stb, o_frame_err, o_parity_err, o_busy, state, i_ps2 };

endmodule
