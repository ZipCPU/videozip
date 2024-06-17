////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/proto/mondata.v
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
// }}}
module	mondata (
		// {{{
		input	wire		i_clk, i_reset,
		input	wire		S_VALID,
		output	wire		S_READY,
		input	wire	[7:0]	S_DATA,
		input	wire		S_LAST,
		input	wire		S_ABORT,
		output	reg		o_drop,
		output	reg	[31:0]	o_drop_count,
		output	reg		o_data_packet
		// }}}
	);

	reg	[9:0]	byte_count, last_framecount;
	reg		is_data_packet;
	reg	[31:0]	tmp_cfg_word;
	wire	[9:0]	frames_lost, next_framecount;
	reg		first_frame;

	// byte_count
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		byte_count <= 0;
	else if (S_ABORT && (S_READY || !S_VALID))
		byte_count <= 0;
	else if (S_VALID && S_READY && S_LAST)
		byte_count <= 0;
	else if (S_VALID && S_READY && !(&byte_count))
		byte_count <= byte_count + 1;
	// }}}

	// is_data_packet
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		is_data_packet <= 0;
	else if (S_VALID && S_READY)
	case(byte_count)
	// Ethernet header
	10'h000: is_data_packet <= 1'b1;
	10'h00c: is_data_packet <= is_data_packet && S_DATA == 8'h08;
	10'h00d: is_data_packet <= is_data_packet && S_DATA == 8'h00;
	// IP Header
	10'h00e: is_data_packet <= is_data_packet && S_DATA == 8'h45;
	10'h017: is_data_packet <= is_data_packet && S_DATA == 8'h11;
	// UDP Header
	// Dataport == 8546, for both source and destination
	10'h022: is_data_packet <= is_data_packet && S_DATA == 8'h21;
	10'h023: is_data_packet <= is_data_packet && S_DATA == 8'h62;
	10'h024: is_data_packet <= is_data_packet && S_DATA == 8'h21;
	10'h025: is_data_packet <= is_data_packet && S_DATA == 8'h62;
	10'h02a: is_data_packet <= is_data_packet && S_DATA[7] == 1'b0;
	//
	default: begin end
	endcase
	// }}}

	// tmp_cfg_word
	// {{{
	always @(posedge i_clk)
	if (i_reset)
		tmp_cfg_word <= 0;
	else if (S_VALID && S_READY)
	case(byte_count)
	10'h02a: tmp_cfg_word[31:24] <= S_DATA; //
	10'h02b: tmp_cfg_word[23:16] <= S_DATA; //
	10'h02c: tmp_cfg_word[15: 8] <= S_DATA; // ...
	10'h02d: tmp_cfg_word[ 7: 0] <= S_DATA; // First byte of data
	default: begin end
	endcase
	// }}}

	// last_framecount, first_frame
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		last_framecount <= 0;
		first_frame <= 1'b1;
	end else if (S_VALID && S_READY && S_LAST && !S_ABORT
			&& is_data_packet && byte_count > 10'd300)
	begin
		first_frame <= 1'b0;
		last_framecount <= tmp_cfg_word[23:14];
	end
	// }}}

	assign	next_framecount = last_framecount + 1;
	assign	frames_lost = tmp_cfg_word[23:14] - next_framecount;

	// o_drop, o_drop_count, o_data_packet
	// {{{
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_drop <= 1'b0;
		o_drop_count <= 32'h0;
		o_data_packet <= 1'b0;
	end else if (S_VALID && S_READY && S_LAST && !S_ABORT
			&& is_data_packet && byte_count > 10'd300)
	begin
		if (tmp_cfg_word[23:14] != next_framecount && !first_frame)
		begin
			o_drop <= 1'b1;
			o_drop_count <= o_drop_count + { 22'h0, frames_lost };
		end

		o_data_packet <= 1'b1;
	end else begin
		o_drop <= 1'b0;
		o_data_packet <= 1'b0;
	end
	// }}}

	assign	S_READY = 1'b1;

	// Verilator lint_off UNUSED
	wire	unused;
	assign	unused = &{ 1'b0, tmp_cfg_word[31:24], tmp_cfg_word[13:0] };
	// Verilator lint_on  UNUSED
endmodule
