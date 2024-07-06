////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rtl/video/vid_crop.v
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
// Copyright (C) 2024, Gisselquist Technology, LLC
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
module	vid_crop #(
		parameter	LGDIM = 12,
		parameter	PW = 24
		// parameter	OPT_TUSER_IS_SOF = 1'b0
	) (
		// {{{
		input	wire			i_clk, i_reset,
		//
		input	wire			i_cfg_en,
		input	wire	[LGDIM-1:0]	i_cfg_hpos,
						i_cfg_vpos,
		input	wire	[LGDIM-1:0]	i_cfg_width,
						i_cfg_height,
		//
		input	wire			S_VALID,
		output	wire			S_READY,
		input	wire	[PW-1:0]	S_DATA,
		input	wire			S_HLAST,
		input	wire			S_VLAST,
		//
		output	wire			M_VALID,
		input	wire			M_READY,
		output	wire	[PW-1:0]	M_DATA,
		output	wire			M_HLAST,
		output	wire			M_VLAST
		// }}}
	);

	// Local declarations
	// {{{
	reg	[LGDIM-1:0]	hpos, vpos;
	wire			skd_valid, skd_ready, skd_hlast, skd_vlast;
	wire	[PW-1:0]	skd_data;

	reg			vlast, hlast, past_vlast, past_hlast;

	reg			r_valid, r_hlast, r_vlast;
	reg	[PW-1:0]	r_data;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Skidbuffer
	// {{{
	skidbuffer #(
`ifdef	FORMAL
		.OPT_PASSTHROUGH(1'b1),
`else
		.OPT_PASSTHROUGH(1'b0),
`endif
		.DW(2+PW)
	) u_skd (
		.i_clk(i_clk), .i_reset(i_reset),
		.i_valid(S_VALID), .o_ready(S_READY),
			.i_data({ S_VLAST, S_HLAST, S_DATA }),
		.o_valid(skd_valid), .i_ready(skd_ready),
			.o_data({ skd_vlast, skd_hlast, skd_data })
	);

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Position tracking: hpos, vpos
	// {{{

	// hpos, vpos
	always @(posedge i_clk)
	if (i_reset)
	begin
		hpos <= 0;
		vpos <= 0;
	end else if (skd_valid && skd_ready)
	begin
		hpos <= hpos + 1;
		if (skd_hlast)
		begin
			hpos <= 0;
			vpos <= vpos + 1;
			if (skd_vlast)
				vpos <= 0;
		end
	end

	// r_vlast, past_vlast, past_hlast
	always @(posedge i_clk)
	if (i_reset)
	begin
		vlast <= 1'b0;
		hlast <= 1'b0;
		past_vlast <= 1'b0;
		past_hlast <= 1'b0;
	end else if (!i_cfg_en)
	begin
		vlast <= 1'b0;
		hlast <= 1'b0;
		past_vlast <= 1'b0;
		past_hlast <= 1'b0;
	end else if (skd_valid && skd_ready)
	begin
		hlast    <= (i_cfg_width <= 1)
			||(hpos + 2 >= i_cfg_width + i_cfg_hpos);
		past_hlast <= (i_cfg_width <= 1)
			||(hpos + 1 >= i_cfg_width + i_cfg_hpos);
		vlast    <= (vpos + (skd_hlast || hlast) + 1 >= i_cfg_height + i_cfg_vpos);

		if (!past_vlast)
		begin
			if ((skd_hlast || hlast) && !past_hlast)
			begin
				past_vlast <= r_vlast;
			end
		end
		//past_vlast <= past_vlast
		//	||((skd_hlast || hlast) && (skd_vlast || (vlast && hlast)));

		if (skd_hlast)
		begin
			hlast <= (i_cfg_width <= 1);
			past_hlast <= 1'b0;
		end

		if (skd_hlast && skd_vlast)
		begin
			past_vlast <= 1'b0;
			vlast    <= (i_cfg_height <= 1);
		end
	end else begin
		if (i_cfg_width == 0)
			past_hlast <= 1;
		if (i_cfg_height == 0)
			past_vlast <= 1;
	end

	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// Output generation
	// {{{

	initial	r_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_valid <= 1'b0;
	else if (skd_valid && skd_ready)
	begin
		r_valid <= 1'b0;
		if (!i_cfg_en)
			r_valid <= 1'b1;
		else if ((hpos >= i_cfg_hpos)&&(vpos >= i_cfg_vpos)
				&& !past_hlast && !past_vlast)
			r_valid <= 1'b1;
	end else if (skd_ready)
		r_valid <= 1'b0;

	always @(posedge i_clk)
	if (skd_valid && skd_ready)
		r_data <= skd_data;

	always @(posedge i_clk)
	if (i_reset)
		r_hlast <= 1'b0;
	else if (skd_valid && skd_ready)
	begin
		r_hlast <= 1'b0;
		if (skd_hlast || (i_cfg_en && hlast))
			r_hlast <= 1'b1;
	end

	always @(posedge i_clk)
	if (i_reset)
		r_vlast <= 1'b0;
	else if (skd_valid && skd_ready)
	begin
		r_vlast <= 1'b0;
		if (skd_vlast || (i_cfg_en && vlast && !past_hlast))
			r_vlast <= !past_vlast;
		if (r_valid && r_hlast && r_vlast)
			r_vlast <= 1'b0;
	end else if (M_VALID && M_READY && M_HLAST)
		r_vlast <= 1'b0;
	// }}}

	assign	M_VALID = r_valid;
	assign	M_DATA  = r_data;
	assign	M_HLAST = r_hlast;
	assign	M_VLAST = r_vlast;

	assign	skd_ready = !M_VALID || M_READY;
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// Formal properties
// {{{
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
`ifdef	FORMAL
	(* anyconst *)	reg	[LGDIM-1:0]	fc_width, fc_height;
	(* anyconst *)	reg	[LGDIM-1:0]	f_cfg_width, f_cfg_height,
						f_cfg_hpos, f_cfg_vpos;
	(* anyconst *) reg fc_en;
	reg	[LGDIM-1:0]	f_crop_width, f_crop_height;
	wire	[LGDIM-1:0]	fs_xpos, fs_ypos, fm_xpos, fm_ypos;
	wire			fs_known, fm_known,
				fs_hlast, fs_vlast, fs_sof,
				fm_hlast, fm_vlast, fm_sof;

	reg	f_past_valid;

	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1;

	always @(*)
	if (!f_past_valid)
		assume(i_reset);

	always @(posedge i_clk)
	if (!f_past_valid || $past(i_reset))
		assume(!S_VALID);
	else if ($past(S_VALID && !S_READY))
	begin
		assume(S_VALID);
		assume($stable(S_DATA));
		assume($stable(S_HLAST));
		assume($stable(S_VLAST));
	end

	always @(*)
	begin
		assume(i_cfg_en == fc_en);
		assume(i_cfg_width  == f_cfg_width);
		assume(i_cfg_height == f_cfg_height);
		assume(i_cfg_hpos == f_cfg_hpos);
		assume(i_cfg_vpos == f_cfg_vpos);

		assume(fc_width  > 2);
		assume(fc_height > 2);
		assume(f_cfg_width  > 2);
		assume(f_cfg_height > 2);
	end

	always @(*)
	begin
		if (!i_cfg_en)
			f_crop_width = fc_width;
		else if (f_cfg_hpos >= fc_width)
			f_crop_width = 0;
		else if ({ 1'b0, f_cfg_hpos } + { 1'b0, f_cfg_width } <= { 1'b0, fc_width })
			f_crop_width = f_cfg_width;
		else
			f_crop_width = fc_width - f_cfg_hpos;

		if (!i_cfg_en)
			f_crop_height = fc_height;
		else if (f_cfg_vpos >= fc_height)
			f_crop_height = 0;
		else if ({ 1'b0, f_cfg_vpos } + { 1'b0, f_cfg_height } <= { 1'b0, fc_height })
			f_crop_height = f_cfg_height;
		else
			f_crop_height = fc_height - f_cfg_vpos;
	end

	faxivideo #(
		.LGDIM(LGDIM), .OPT_TUSER_IS_SOF(0)
	) fsrc (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.S_VID_TVALID(S_VALID), .S_VID_TREADY(S_READY),
		.S_VID_TDATA(S_DATA), .S_VID_TLAST(S_VLAST && S_HLAST),
		.S_VID_TUSER(S_HLAST),
		.i_width(fc_width), .i_height(fc_height),
		.o_xpos(fs_xpos), .o_ypos(fs_ypos),
		.f_known_height(fs_known),
		.o_hlast(fs_hlast), .o_vlast(fs_vlast), .o_sof(fs_sof)
	);

	always @(*)
	if (S_VALID)
	begin
		assume(S_HLAST == fs_hlast);
		assume(S_VLAST == fs_vlast);
	end

	always @(posedge i_clk)
	if (f_past_valid)
	begin
		assert(fs_xpos == hpos);
		assert(fs_ypos == vpos);
	end

	always @(posedge i_clk)
	if (f_past_valid && fs_xpos <= i_cfg_hpos)
		assert(!hlast && !past_hlast);

	always @(posedge i_clk)
	if (f_past_valid && fs_ypos <= i_cfg_vpos)
		assert(!vlast && !past_vlast);

	always @(posedge i_clk)
	if (f_past_valid && (fs_xpos != 0 || fs_ypos != 0 || fs_known) && i_cfg_en)
	begin
		assert(hlast == ({ 1'b0, fs_xpos } + 1 >= i_cfg_hpos + i_cfg_width));
		assert(past_hlast == ({ 1'b0, fs_xpos } >= i_cfg_width  + i_cfg_hpos));
		if (hpos == 0) assert(!past_hlast);

		assert(vlast == ({ 1'b0, fs_ypos } + (past_hlast ? 1:0) + 1 >= i_cfg_height + i_cfg_vpos));
		if ({ 1'b0, i_cfg_vpos } + { 1'b0, i_cfg_height } > fc_height)
		begin
			assert(past_vlast == (fs_ypos + (past_hlast ? 1:0) >= { 1'b0, fc_height }));
		end else if ({ 1'b0, i_cfg_vpos } + { 1'b0, i_cfg_height } == fc_height)
		begin
			assert(past_vlast ==
				({ 1'b0, fs_ypos } + (past_hlast ? 1:0)
							>= fc_height));
		end else
			assert(past_vlast ==
				({ 1'b0, fs_ypos } + (past_hlast ? 1:0)
				>= { 1'b0, i_cfg_height } + { 1'b0, i_cfg_vpos }));
		if (vpos == 0) assert(!past_vlast);
	end

	faxivideo #(
		.LGDIM(LGDIM), .OPT_TUSER_IS_SOF(0)
	) fout (
		.i_clk(i_clk), .i_reset_n(!i_reset),
		.S_VID_TVALID(M_VALID), .S_VID_TREADY(M_READY),
		.S_VID_TDATA(M_DATA), .S_VID_TLAST(M_VLAST && M_HLAST),
		.S_VID_TUSER(M_HLAST),
		.i_width(f_crop_width), .i_height(f_crop_height),
		.o_xpos(fm_xpos), .o_ypos(fm_ypos),
		.f_known_height(fm_known),
		.o_hlast(fm_hlast), .o_vlast(fm_vlast), .o_sof(fm_sof)
	);

	always @(*)
	if (f_past_valid)
	begin
		assert((M_VLAST == (fm_ypos + 1 == f_crop_height))
			||(!M_VLAST && fm_xpos == 0));
	end

	always @(*)
	if (f_past_valid && M_VALID)
	begin
		assert(M_HLAST == fm_hlast);
		assert(M_VLAST == fm_vlast);

		assert(i_cfg_width  > 0);
		assert(i_cfg_height > 0);

		if (!fc_en)
		begin
			// Covered elsewhere below
		end else if (M_VALID && M_HLAST && M_VLAST)
		begin
			assert(fs_xpos == 0 || past_hlast);
			assert(fs_ypos == 0 || past_vlast);
		end else if (M_VALID && M_HLAST)
		begin
			assert(fs_xpos == 0 || past_hlast);
			if (fs_ypos < i_cfg_vpos)
				assert(fm_ypos == 0);
			else
				assert(fm_ypos + i_cfg_vpos + (past_hlast ? 0:1) == fs_ypos);
		end else if (fs_ypos < i_cfg_vpos)
		begin
			assert(fm_xpos == 0);
			assert(fm_ypos == 0);
		end else if (fs_xpos < i_cfg_hpos)
		begin
			assert(fm_xpos == 0 || (M_VALID && M_HLAST));
			if (hpos < i_cfg_hpos + i_cfg_width)
			begin
				assert((M_VALID && M_HLAST) || fm_ypos == fs_ypos - i_cfg_vpos);
			end else // if (hpos < i_cfg_hpos + i_cfg_width)
				assert((M_VALID && M_HLAST) || fm_ypos == fs_ypos - i_cfg_vpos + 1);
		end else if (fs_xpos > 0)
		begin
			assert(fm_xpos + 1 == fs_xpos - i_cfg_hpos);
			assert(fm_ypos     == fs_ypos - i_cfg_vpos);
		end
	end

	always @(*)
	if (f_past_valid)
	begin
		// Relate fm_?pos to fs_?pos when not !M_VALID
		if (!fc_en)
		begin
			if (M_VALID)
			begin
				if (fs_xpos == 0)
				begin
					assert(fm_xpos == fc_width-1);
					if (fs_ypos == 0)
					begin
						assert(fm_ypos + 1== fc_height);
					end else
						assert(fm_ypos + 1 == fs_ypos);
				end else begin
					assert(fm_xpos + 1 == fs_xpos);
					assert(fm_ypos == fs_ypos);
				end
			end else begin
				assert(fm_xpos == fs_xpos);
				assert(fm_ypos == fs_ypos);
			end
		end else if (M_VALID && M_HLAST && M_VLAST)
		begin
			assert(fs_xpos == 0 || past_hlast);
			assert(fs_ypos == 0 || past_vlast);
		end else if (M_VALID && M_HLAST)
		begin
			assert({ 1'b0, fs_ypos } == fm_ypos + { 1'b0, i_cfg_vpos } + (past_hlast ? 0:1));

		//	assert(fs_xpos == 0 || past_hlast);
		//	if (fs_ypos < i_cfg_vpos)
		//		assert(fm_ypos == 0);
		//	else
		//		assert(fm_ypos + i_cfg_vpos + (past_hlast ? 0:1) == fs_ypos);
		end else if (fs_ypos < i_cfg_vpos)
		begin // Before the first line
			// {{{
			assert(!M_VALID);
			assert(fm_xpos == 0);
			assert(fm_ypos == 0);
			// }}}
		end else if (fs_ypos == i_cfg_vpos)
		begin // First line
			// {{{
			if (fs_xpos < i_cfg_hpos)
			begin
				assert(!M_VALID);
				assert(fm_xpos == 0);
				assert(fm_ypos == 0);
			end else if ({ 1'b0, fs_xpos } < { 1'b0, i_cfg_hpos } + { 1'b0, i_cfg_width })
			begin
				assert(fm_xpos + (M_VALID ? 1:0) == fs_xpos - i_cfg_hpos);
				assert(fm_ypos == 0);
			end else // if (fs_xpos < i_cfg_hpos + i_cfg_width)
			begin
				assert(M_VALID || (fm_xpos == 0 && past_hlast));
				assert(fm_ypos == (past_hlast ? 1:0));
			end
			// }}}
		end else if ({ 1'b0, fs_ypos } < { 1'b0, i_cfg_vpos } + { 1'b0, i_cfg_height })
		begin
			// {{{
			if (fs_xpos <= i_cfg_hpos)
			begin
				assert(!M_VALID);
				assert(fm_xpos == 0);
				assert(fm_ypos == fs_ypos - i_cfg_vpos);
			end else if (fs_xpos < { 1'b0, i_cfg_hpos } + { 1'b0, i_cfg_width })
			begin
				assert(fm_xpos + (M_VALID ? 1:0) == fs_xpos - i_cfg_hpos);
				assert(fm_ypos == fs_ypos - i_cfg_vpos);
			end else // if (fs_xpos < i_cfg_hpos + i_cfg_width)
			begin
				assert(fm_xpos == 0);
				assert(M_VALID || fs_xpos == 0 || past_hlast);
				if (past_vlast)
				begin
					assert(fm_ypos == 0);
				end else if (past_hlast)
				begin
					assert(fm_ypos == fs_ypos - i_cfg_vpos + 1);
				end else begin
					assert(fm_ypos == fs_ypos - i_cfg_vpos);
				end
				// assert(fm_ypos == fs_ypos - i_cfg_vpos);
			end
			// }}}
		end else // if (fs_ypos < i_cfg_vpos + i_cfg_height)
		begin // Beyond the last line
			// {{{
			assert(!M_VALID);
			assert(past_vlast);
			assert(fm_xpos == 0);
			assert(fm_ypos == 0);
			// }}}
		end
	end

	always @(*)
	if (f_past_valid)
	begin
		// Relate fm_?pos to past_?last
		if (!fc_en)
		begin
			assert(!hlast);
			assert(!vlast);
			assert(!past_hlast);
			assert(!past_vlast);
		end else if (M_VALID && M_HLAST)
		begin
			// M_?LAST already relates to fm_?pos, only need to
			// relate it to fs_?pos.
			assert(past_hlast == (fs_xpos != 0));
			if (past_hlast)
				assert(fs_xpos >= { 1'b0, i_cfg_hpos} + { 1'b0, i_cfg_width });
			if (M_VLAST)
			begin
				assert(past_vlast == (fs_ypos != 0));
				if (past_hlast) assert(past_vlast);
			end else
				assert(!past_vlast);
		end else begin
			assert(!past_hlast || fm_xpos == 0);
			assert(!past_vlast || (fm_xpos == 0 && fm_ypos == 0));
		end
	end

	////////////////////////////////////////////////////////////////////////
	//
	// "Careless" assumptions
	// {{{

	always @(*)
	begin
		assume(f_crop_width  > 1);
		assume(f_crop_height > 1);
	end
	// }}}
`endif
// }}}
endmodule
