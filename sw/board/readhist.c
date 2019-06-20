////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	readhist.c
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
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
#include <stdint.h>
#include <design.h>
#include <cpudefs.h>
#include "board.h"
#include "zipcpu.h"
#include "zipsys.h"
#include "txfns.h"

asm("\t.section\t.start\n"
	"\t.global\t_start\n"
	"\t.type\t_start,@function\n"
"_start:\n"
	"\tLDI\t_top_of_stack,SP\n"
	"\tCLR\tCC\n"
	"\tMOV\tbusy_failure(PC),R0\n"
	"\tBRA\tentry\n"
"busy_failure:\n"
	"\tBUSY\n"
	"\t.section\t.text\n");

void	wait_int(unsigned imsk) {
	_zip->z_pic = DALLPIC|imsk;
	_zip->z_pic = EINT(imsk);
	zip_idle();
}

unsigned	heartbeats = 0;
unsigned	hdata[3*1024];

void entry(void) {
	unsigned	v;
	int		valid_edid = 0;

	txstr("\n\nREAD-HIST\n\n");

	heartbeats = 0;

	while(1) {
		unsigned	*hp = hdata;
		wait_int(SYSPIC_PPS);
		for(unsigned i=0; i<1024; i++) {
			_hist->h_ctrl = HIST_SET(i);
			wait_int(SYSPIC_PPS);
			wait_int(SYSPIC_PPS);
			*hp++ = _hist->h_red;
			*hp++ = _hist->h_green;
			*hp++ = _hist->h_blue;
			txstr("*");
			heartbeats++;
		} txstr("\n0x"); txhex(heartbeats); txstr(" HeartBeats,");
		txstr("  0x"); txhex((unsigned)hdata); txstr(" Address\n");
	}
}
