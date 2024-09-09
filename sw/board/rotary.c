////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/rotary.c
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
#include "board.h"
#include "txfns.h"
#include "zipcpu.h"
// }}}

int main(int argc, char **argv) {
#ifndef	_BOARD_HAS_ROTARY
	txstr("ERR: This software depends upon the presence of rotary encoder\n"
		"hardware within the design, hardware which has not been\n"
		"included as of this build.\n");
	zip_halt().
#else
	unsigned	last;

	txstr(
"+----------------------------------+\n"
"|-        Rotary PMOD Test        -|\n"
"+----------------------------------+\n\n");

	*_rotary = last = 0;
	txstr("Rotary value: 0x"); txhex(last); txstr("\r\n");
	while(1) {
		int	r = *_rotary;
		if (r < 0)
			*_rotary = r = 0;
		if ((unsigned)r != last) {
			last = (unsigned)r;
			txstr("Rotary value: 0x"); txhex(last); txstr("\r\n");
		}
	}
#endif
}
