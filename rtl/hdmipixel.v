////////////////////////////////////////////////////////////////////////////////
//
// Filename:	hdmipixel.v
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To find one particular pixel among a frame of pixels.
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
module	hdmipixel(i_wb_clk, i_hclk, i_hdmi_r, i_hdmi_g, i_hdmi_b,
		i_wb_cyc, i_wb_stb, i_wb_we, i_wb_addr, i_wb_data,
		o_wb_stall, o_wb_ack, o_wb_data);
	parameter	CLKBITS = 30;
	input	wire	i_wb_clk;
	// HDMI inputs
	input	wire		i_hclk;
	input	wire	[9:0]	i_hdmi_r, i_hdmi_g, i_hdmi_b;
	// Wishbone
	// 	WB inputs
	input	wire		i_wb_cyc, i_wb_stb, i_wb_we;
	input	wire	[1:0]	i_wb_addr;
	input	wire	[31:0]	i_wb_data;
	//	WB outputs
	output	reg		o_wb_ack;
	output	wire		o_wb_stall;
	output	reg	[31:0]	o_wb_data;

	reg			new_clks, new_clks_ack,
				new_pixel, new_pixel_ack;
	reg	[(CLKBITS-1):0]	wb_frame_clks, wb_frame_pixel;
	always @(posedge i_wb_clk)
	begin
		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr == 2'b00))
		begin
			wb_frame_clks[(CLKBITS-1):0]<= i_wb_data[(CLKBITS-1):0];
			new_clks <= 1'b1;
		end else if (new_clks_ack)
			new_clks <= 1'b0;

		if ((i_wb_stb)&&(i_wb_we)&&(i_wb_addr == 2'b01))
		begin
			wb_frame_pixel[(CLKBITS-1):0]<= i_wb_data[(CLKBITS-1):0];
			new_pixel <= 1'b1;
		end else if (new_pixel_ack)
			new_pixel <= 1'b0;
	end

	//
	// Transfer new_clks to the HDMI clock
	//
	reg		hs_new_clks;
	reg	[1:0]	new_clk_transfer;
	always @(posedge i_hclk)
		{hs_new_clks, new_clk_transfer} <= {new_clk_transfer, new_clks};

	// Transfer the response back
	reg		hs_new_clks_ack;
	reg	[1:0]	new_clks_ack_transfer;
	always @(posedge i_hclk)
		{ new_clks_ack, new_clks_ack_transfer }
			<= { new_clks_ack_transfer, hs_new_clks };



	//
	// Transfer new_pixel to the HDMI clock
	//
	reg		hs_new_pixel;
	reg	[1:0]	new_pixel_transfer;
	always @(posedge i_hclk)
		{ hs_new_pixel, new_pixel_transfer }
			<= { new_pixel_transfer, new_pixel };

	// Transfer the response back
	reg		hs_new_pixel_ack;
	reg	[1:0]	new_pixel_ack_transfer;
	always @(posedge i_hclk)
		{ new_pixel_ack, new_pixel_ack_transfer }
			<= { new_pixel_ack_transfer, hs_new_pixel };


	reg	[(CLKBITS-1):0]	hs_frame_clks, hs_frame_pixel;
	// Now, grab the data we need
	always @(posedge i_hclk)
		if (hs_new_clks)
			hs_frame_clks <= wb_frame_clks;

	always @(posedge i_hclk)
		if (hs_new_pixel)
			hs_frame_pixel <= wb_frame_pixel;

	reg	[(CLKBITS-1):0]	hs_frame_counter;
	always @(posedge i_hclk)
		if (hs_frame_counter < hs_frame_clks)
		begin
			hs_frame_counter <= hs_frame_counter + 1'b1;
		end else begin
			hs_frame_counter <= 0;
		end

	reg	grab_pixel;
	always @(posedge i_hclk)
		grab_pixel <= (hs_frame_counter == hs_frame_pixel);

	reg	[29:0]	hs_pixel_data;
	always @(posedge i_hclk)
		if (grab_pixel)
			hs_pixel_data <= { i_hdmi_r, i_hdmi_g, i_hdmi_b };
	
	reg		slow_grab;
	reg	[5:0]	grab_pipe;
	always @(posedge i_hclk)
		grab_pipe <= { grab_pipe[4:0], grab_pixel };
	always @(posedge i_hclk)
		slow_grab <= (grab_pipe != 6'h0);

	reg	wb_grab_stb;
	reg	[2:0]	slow_grab_pipe;
	always @(posedge i_wb_clk)
		slow_grab_pipe <= { slow_grab_pipe[1:0], slow_grab };
	always @(posedge i_wb_clk)
		wb_grab_stb <= ((!slow_grab_pipe[2])&&(slow_grab_pipe[1]));

	reg	[29:0]	wb_pixel_data;
	always @(posedge i_wb_clk)
		if (wb_grab_stb)
			wb_pixel_data <= hs_pixel_data;

	always @(posedge i_wb_clk)
		casez(i_wb_addr)
		2'b00 : o_wb_data <= {{ (32-CLKBITS){1'b0} }, wb_frame_clks };
		2'b01 : o_wb_data <= {{ (32-CLKBITS){1'b0} }, wb_frame_pixel };
		2'b1? : o_wb_data <= { 2'b00, wb_pixel_data };
		endcase
	always @(posedge i_wb_clk)
		o_wb_ack <= i_wb_stb;
	assign	o_wb_stall = 1'b0;

endmodule
