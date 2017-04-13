////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	smpladc.v
//
// Project:	WBPMIC, wishbone control of a MEMs PMod MIC
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
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
module	smpladc(i_clk, i_request, i_rd, i_en, o_csn, o_sck, i_miso, o_data);
	parameter [8:0]	CKPCK = 2;
	input	wire		i_clk, i_request, i_rd, i_en;
	output	wire		o_csn;
	output	reg		o_sck;
	input	wire		i_miso;
	output	wire	[13:0]	o_data;


	reg	[8:0]	r_clk;
	reg		active, last_en, valid_stb, zclk, r_valid, hclk;
	reg	[4:0]	m_clk;
	reg	[15:0]	r_data;
	reg	[11:0]	r_output;

	initial	active    = 1'b0;
	initial	last_en   = 1'b0;
	initial	valid_stb = 1'b0;
	initial	m_clk     = 5'h0;
	initial	zclk      = 1'b0;
	initial	o_sck     = 1'b1;
	always @(posedge i_clk)
	begin
		if ((i_request)&&(!active))
			last_en <= i_en;
		if ((i_request)&&(!active)&&((i_en)||(last_en)))
			active <= 1'b1;
		else if ((hclk)&&(o_sck)&&(m_clk >= 5'h0a)&&(!i_en))
			active <= 1'b0;
		else if ((hclk)&&(o_sck)&&(m_clk >= 5'h10))
			active <= 1'b0;

		valid_stb <= ((hclk)&&(o_sck)&&(m_clk >= 5'h10));

		if (!active)
			m_clk <= 5'h0;
		else if (zclk)
			m_clk <= m_clk + 1'b1;

		zclk <= 1'b0;
		hclk <= 1'b0;
		if ((active)||(!o_sck))
		begin
			if (r_clk == CKPCK)
			begin
				hclk <= 1'b1;
				zclk  <= o_sck;
				o_sck <= (!o_sck)||(!active);
				r_clk <= 0;
			end else
				r_clk <= r_clk + 1'b1;
		end else begin
			r_clk <= 0;
			o_sck <= 1'b1;
		end
	end
	assign	o_csn = !active;

	initial	r_valid = 1'b0;
	always @(posedge i_clk)
		if (i_rd)
			r_valid <= (valid_stb);
		else
			r_valid <= (r_valid)||(valid_stb);

	always @(posedge i_clk)
		if (zclk)
			r_data <= { r_data[14:0], i_miso };

	always @(posedge i_clk)
		if ((hclk)&&(o_sck)&&(m_clk >= 5'h10))
			r_output <= r_data[11:0];

	assign	o_data = { !last_en, r_valid, r_output };

endmodule

