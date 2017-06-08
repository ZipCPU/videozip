////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	wbquadarbiter.v
//
// Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015,2017, Gisselquist Technology, LLC
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
`define	WBA_ALTERNATING
module	wbquadarbiter(i_clk, i_rst, 
	// Bus A
	i_a_cyc, i_a_stb, i_a_we, i_a_adr, i_a_dat, i_a_sel, o_a_ack, o_a_stall, o_a_err,
	// Bus B
	i_b_cyc, i_b_stb, i_b_we, i_b_adr, i_b_dat, i_b_sel, o_b_ack, o_b_stall, o_b_err,
	// Bus C
	i_c_cyc, i_c_stb, i_c_we, i_c_adr, i_c_dat, i_c_sel, o_c_ack, o_c_stall, o_c_err,
	// Bus D
	i_d_cyc, i_d_stb, i_d_we, i_d_adr, i_d_dat, i_d_sel, o_d_ack, o_d_stall, o_d_err,
	// Both buses
	o_cyc, o_stb, o_we, o_adr, o_dat, o_sel, i_ack, i_stall, i_err);
	// 18 bits will address one GB, 4 bytes at a time.
	// 19 bits will allow the ability to address things other than just
	// the 1GB of memory we are expecting.
	parameter			DW=32, AW=19;
	// Wishbone doesn't use an i_ce signal.  While it could, they dislike
	// what it would (might) do to the synchronous reset signal, i_rst.
	input	wire			i_clk, i_rst;
	input	wire	[(AW-1):0]	i_a_adr, i_b_adr, i_c_adr, i_d_adr;
	input	wire	[(DW-1):0]	i_a_dat, i_b_dat, i_c_dat, i_d_dat;
	input	wire	[(DW/8-1):0]	i_a_sel, i_b_sel, i_c_sel, i_d_sel;
	input	wire			i_a_we, i_a_stb, i_a_cyc;
	input	wire			i_b_we, i_b_stb, i_b_cyc;
	input	wire			i_c_we, i_c_stb, i_c_cyc;
	input	wire			i_d_we, i_d_stb, i_d_cyc;
	output	wire		o_a_ack,   o_b_ack,   o_c_ack,   o_d_ack,
				o_a_stall, o_b_stall, o_c_stall, o_d_stall,
				o_a_err,   o_b_err,   o_c_err,   o_d_err;
	output	wire	[(AW-1):0]	o_adr;
	output	wire	[(DW-1):0]	o_dat;
	output	wire	[(DW/8-1):0]	o_sel;
	output	wire			o_we, o_stb, o_cyc;
	input	wire			i_ack, i_stall, i_err;

	reg	[1:0]	r_owner;
	generate
	if (METHOD == "PRIORITY")
	begin
		always @(posedge i_clk)
		if (i_rst)
		begin
			r_owner <= 2'b00; // A
		end else casex({r_owner, i_a_cyc, i_b_cyc, i_c_cyc, i_d_cyc })
		6'h001???: r_owner <= 2'b00;	// Maintain ownership
		6'h0001??: r_owner <= 2'b01;
		6'h00001?: r_owner <= 2'b10;
		6'h000001: r_owner <= 2'b11;	// (Last choice)
		//
		6'h0110??: r_owner <= 2'b00;
		6'h01?1??: r_owner <= 2'b01;	// Maintain ownership
		6'h01001?: r_owner <= 2'b10;
		6'h010001: r_owner <= 2'b11;	// (Last choice)
		//
		6'h101?0?: r_owner <= 2'b00;
		6'h10010?: r_owner <= 2'b01;
		6'h10001?: r_owner <= 2'b10;	// Maintain ownership
		6'h100001: r_owner <= 2'b11;	// (Last choice)
		//
		6'h111??0: r_owner <= 2'b00;
		6'h1101?0: r_owner <= 2'b01;
		6'h110010: r_owner <= 2'b10;
		6'h11???1: r_owner <= 2'b11;	// Maintain ownership
		//
		default:   r_owner <= 2'b00;
		endcase
	//
	end else // if (METHOD == "ROUND_ROBIN")
	begin
	//
		always @(posedge i_clk)
		if (i_rst)
		begin
			r_owner <= 2'b0;
		end else casex({r_owner, i_a_cyc, i_b_cyc, i_c_cyc, i_d_cyc })
		6'h001???: r_owner <= 2'b00;	// Maintain ownership
		6'h0001??: r_owner <= 2'b01;
		6'h00001?: r_owner <= 2'b10;
		6'h000001: r_owner <= 2'b11;	// (Last choice)
		//
		6'h011000: r_owner <= 2'b00;	// (Last choice)
		6'h01?1??: r_owner <= 2'b01;	// Maintain ownership
		6'h01?01?: r_owner <= 2'b10;
		6'h01?001: r_owner <= 2'b11;
		//
		6'h101?00: r_owner <= 2'b00;
		6'h100100: r_owner <= 2'b01;	// (Last choice)
		6'h10??1?: r_owner <= 2'b10;	// Maintain ownership
		6'h10??01: r_owner <= 2'b11;
		//
		6'h111??0: r_owner <= 2'b00;
		6'h1101?0: r_owner <= 2'b01;
		6'h110010: r_owner <= 2'b10;	// (Last choice)
		6'h11???1: r_owner <= 2'b11;	// Maintain ownership
		//
		default:   r_owner <= r_owner + 1'b1;
		endcase
	//
		end
	end

	//
	// If you are the owner, retain ownership until i_x_cyc is no
	// longer asserted.  Likewise, you cannot become owner until o_cyc
	// is de-asserted for one cycle.
	//
	// 'A' is given arbitrary priority over 'B'
	// 'A' may own the bus only if he wants it.  When 'A' drops i_a_cyc,
	// o_cyc must drop and so must w_a_owner on the same cycle.
	// However, when 'A' asserts i_a_cyc, he can only capture the bus if
	// it's had an idle cycle.
	// The same is true for 'B' with one exception: if both contend for the
	// bus on the same cycle, 'A' arbitrarily wins.

	// Realistically, if neither master owns the bus, the output is a
	// don't care.  Thus we trigger off whether or not 'A' owns the bus.
	// If 'B' owns it all we care is that 'A' does not.  Likewise, if 
	// neither owns the bus than the values on the various lines are
	// irrelevant.  (This allows us to get two outputs per Xilinx 6-LUT)
	wire	idle;
`ifdef	ZERO_ON_IDLE
	assign	idle = (!o_cyc);
`else
	assign	idle = 1'b1;
`endif

	always @(*)
	begin
		case(r_owner)
		2'b00: begin
			o_cyc = i_a_cyc;
			o_stb = (!idle)&&(i_a_stb);
			o_we  = (!idle)&&(i_a_we);
			o_adr = ( idle) ? 0 : i_a_adr;
			o_dat = ( idle) ? 0 : i_a_dat;
			o_sel = ( idle) ? 0 : i_a_sel;
			end
		2'b01: begin
			o_cyc = i_b_cyc;
			o_stb = (!idle)&&(i_b_stb);
			o_we  = (!idle)&&(i_b_we);
			o_adr = ( idle) ? 0 : i_b_adr;
			o_dat = ( idle) ? 0 : i_b_dat;
			o_sel = ( idle) ? 0 : i_b_sel;
			end
		2'b10: begin
			o_cyc = i_c_cyc;
			o_stb = (!idle)&&(i_c_stb);
			o_we  = (!idle)&&(i_c_we);
			o_adr = ( idle) ? 0 : i_c_adr;
			o_dat = ( idle) ? 0 : i_c_dat;
			o_sel = ( idle) ? 0 : i_c_sel;
			end
		2'b11: begin
			o_cyc = i_d_cyc;
			o_stb = (!idle)&&(i_d_stb);
			o_we  = (!idle)&&(i_d_we);
			o_adr = ( idle) ? 0 : i_d_adr;
			o_dat = ( idle) ? 0 : i_d_dat;
			o_sel = ( idle) ? 0 : i_d_sel;
			end
		endcase
	end

	wire	w_a_owner, w_b_owner, w_c_owner, w_d_owner;
	assign	w_a_owner = (r_owner == 2'b00);
	assign	w_b_owner = (r_owner == 2'b01);
	assign	w_c_owner = (r_owner == 2'b10);
	assign	w_d_owner = (r_owner == 2'b11);

	// We cannot allow the return acknowledgement to ever go high if
	// the master in question does not own the bus.  Hence we force it
	// low if the particular master doesn't own the bus.
	assign	o_a_ack   = (w_a_owner) ? i_ack   : 1'b0;
	assign	o_b_ack   = (w_b_owner) ? i_ack   : 1'b0;
	assign	o_c_ack   = (w_c_owner) ? i_ack   : 1'b0;
	assign	o_d_ack   = (w_d_owner) ? i_ack   : 1'b0;

	// Stall must be asserted on the same cycle the input master asserts
	// the bus, if the bus isn't granted to him.
	assign	o_a_stall = (w_a_owner) ? i_stall : 1'b1;
	assign	o_b_stall = (w_b_owner) ? i_stall : 1'b1;
	assign	o_c_stall = (w_c_owner) ? i_stall : 1'b1;
	assign	o_d_stall = (w_d_owner) ? i_stall : 1'b1;

	//
	//
	assign	o_a_err = (w_a_owner) ? i_err : 1'b0;
	assign	o_b_err = (w_b_owner) ? i_err : 1'b0;
	assign	o_c_err = (w_c_owner) ? i_err : 1'b0;
	assign	o_d_err = (w_d_owner) ? i_err : 1'b0;

endmodule

