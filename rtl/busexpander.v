////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	busexpander.v
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
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
module	busexpander(i_clk,
		i_s_cyc, i_s_stb, i_s_we, i_s_addr, i_s_data, i_s_sel,
			o_s_ack, o_s_stall, o_s_data,
		o_m_cyc, o_m_stb, o_m_we, o_m_addr, o_m_data, o_m_sel,
			i_m_ack, i_m_stall, i_m_data);
	//
	input	wire	i_clk;
	//
	// First wishbone port:
	//
	//	the port with the smaller size
	//
	input	wire			i_s_cyc, i_s_stb, i_s_we;
	input	wire	[(AW-1):0]	i_s_addr;
	input	wire	[(DWIN-1):0]	i_s_data;
	input	wire	[(DWIN/8-1):0]	i_s_sel;
	//
	output	reg			o_s_ack;
	output	reg			o_s_stall;
	output	reg	[(DWIN-1):0]	o_s_data;
	//
	// First wishbone port:
	//
	//	the port with the smaller size
	//
	output	reg			o_m_cyc, o_m_stb, o_m_we;
	output	reg	[(AW-1):0]	o_m_addr;
	output	reg	[(DWOUT-1):0]	o_m_data;
	output	reg	[(DWOUT/8-1):0]	o_m_sel;
	//
	input	wire			i_m_ack;
	input	wire			i_m_stall;
	input	wire	[(DWOUT-1):0]	i_m_data;
	//

	//
	//
	// The output set
	//
	reg	r_stb;
	always @(posedge i_clk)
	begin
		o_wb_cyc <= i_s_cyc;

		if (!i_m_stall)
		begin
			r_stb <= i_s_stb;
			r_we  <= i_s_we;
			//
			r_addr <= i_s_addr[(AW-1):2];
			case(i_s_data[1:0])
			2'b00:	r_data <= {        i_s_data, 96'h00 };
			2'b01:	r_data <= { 32'h0, i_s_data, 64'h00 };
			2'b10:	r_data <= { 64'h0, i_s_data, 32'h00 };
			2'b11:	r_data <= { 96'h0, i_s_data         };
			endcase
			if (!i_s_we)
				r_sel <= 0;
			else case(i_s_data[1:0])
			2'b00:	r_sel <= {        i_s_sel, 12'h00 };
			2'b01:	r_sel <= {  4'h0, i_s_sel,  8'h00 };
			2'b10:	r_sel <= {  8'h0, i_s_sel,  4'h00 };
			2'b11:	r_sel <= { 12'h0, i_s_sel         };
			endcase

			if (r_stb)
			begin
				o_m_stb  <= 1'b1;
				o_m_we   <= r_we;
				o_m_addr <= r_addr;
				o_m_data <= r_data;
				o_m_sel  <= r_sel;
				//
				o_m_stall<= 1'b0;
				r_stb     <= 1'b0;
			end else begin
				o_m_stb  <= 1'b1;
				o_m_we   <= 1'b1;
				o_m_addr <= i_s_addr[(AW-1):2];
				case(i_s_data[1:0])
				2'b00:o_m_data <= {        i_s_data, 96'h00 };
				2'b01:o_m_data <= { 32'h0, i_s_data, 64'h00 };
				2'b10:o_m_data <= { 64'h0, i_s_data, 32'h00 };
				2'b11:o_m_data <= { 96'h0, i_s_data };
				endcase
				if (!i_s_we)
					r_sel <= 0;
				else case(i_s_data[1:0])
				2'b00:o_m_sel <= {        i_s_sel, 12'h00 };
				2'b01:o_m_sel <= {  4'h0, i_s_sel,  8'h00 };
				2'b10:o_m_sel <= {  8'h0, i_s_sel,  4'h00 };
				2'b11:o_m_sel <= { 12'h0, i_s_data        };
				endcase
				//
				o_m_stall <= 1'b0;
				r_stb     <= 1'b0;
			end
		end else if ((!r_stb)&&(!o_m_stall))
		begin
			r_stb <= i_s_stb;
			r_we  <= i_s_we;
			//
			r_addr <= i_s_addr[(AW-1):2];
			case(i_s_data[1:0])
			2'b00:	r_data <= {        i_s_data, 96'h00 };
			2'b01:	r_data <= { 32'h0, i_s_data, 64'h00 };
			2'b10:	r_data <= { 64'h0, i_s_data, 32'h00 };
			2'b11:	r_data <= { 96'h0, i_s_data };
			endcase
			if (!i_s_we)
				r_sel <= 0;
			else case(i_s_data[1:0])
			2'b00:	r_sel <= {        i_s_sel, 12'h00 };
			2'b01:	r_sel <= {  4'h0, i_s_sel,  8'h00 };
			2'b10:	r_sel <= {  8'h0, i_s_sel,  4'h00 };
			2'b11:	r_sel <= { 12'h0, i_s_data        };
			endcase

			o_m_stall <= i_s_stb;
		end

		if (!i_s_cyc)
		begin
			o_m_cyc  <= 1'b0;
			o_m_stb  <= 1'b0;
			r_stb    <= 1'b0;
			o_m_stall  <= 1'b0;
			//
			r_first <= 0;
		end else if ((o_m_stb)&&(!i_s_stall))
			r_first <= r_first + 1'b1;

		fifo[r_first] <= 


		if (!i_s_cyc)
			r_last <= 0;
		end else if (i_m_ack)
			r_last <= r_last + 1'b1;

		o_s_ack  <= i_m_ack;

		o_s_ack <= i_m_ack;
		case(subaddr)
		2'b00: o_s_data <= i_m_data[127:96];
		2'b01: o_s_data <= i_m_data[ 95:64];
		2'b10: o_s_data <= i_m_data[ 63:32];
		2'b11: o_s_data <= i_m_data[ 31: 0];
		endcase
		// o_s_err <= i_m_err;
	end

	wire	[1:0]	subaddr;
	assign	subaddr = fifo[r_last];

endmodule

