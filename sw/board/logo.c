////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/logo.c
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
#include "board.h"
#include "regdefs.h"
#include "txfns.h"
#include "zipcpu.h"
#include "logo.h"
// }}}

int main(int argc, char **argv) {
	unsigned pwr, rtc;
	// char *_sdram = _streamram;

	txstr(
"+----------------------------------+\n"
"|-     B/W OLED Logo Display      -|\n"
"+----------------------------------+\n\n");

	_oled->o_addr = (unsigned)logo;
	while(0 == (_oled->o_cmd & 0x01))
		;

	*_gpio = GPIO_HALT_SET;
	zip_halt();
}
