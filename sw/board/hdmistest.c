////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmistest.c
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

__attribute__((noinline))
void	wait_while_edout_busy(void) {
#ifdef	_BOARD_HAS_HDMI_SRC_EDID
	int	this_edcmd;
	while(_edout->o_cmd & EDID_SRC_BUSY)
		;
#endif
}

void	wait_ms(int ms) {
	const	int	CLOCKS_PER_MS = CLKFREQHZ / 1000;

	while(ms > 0) {
		_zip->z_tma = CLOCKS_PER_MS;
		_zip->z_pic = CLEARPIC;
		_zip->z_pic = EINT(SYSINT_TMA) | SYSINT_TMA;
		if (_zip->z_pic | SYSINT_TMA)
			_zip->z_pic = EINT(SYSINT_TMA) | SYSINT_TMA;
		zip_idle();
		ms--;
	}
}

void entry(void) {
#ifndef	_BOARD_HAS_HDMI_SRC_EDID
	txstr("This program requires an HDMI source port\n");
#else
	unsigned	v;
	int		sync_mask = 0;

	txstr("\n\nHDMI-SYNC-TEST\n\n");
	while(_hin->hin_pixclk < 2000000)
		wait_ms(10);
	for(int i=0; i<32; i++) {
		_hin->hin_ctrl = i | 0x80000000;
		// wait_ms(150);	// 4 frames at 60 Hz / 1000/15
		wait_ms(1500);	// 4 frames at 60 Hz / 1000/15
		txstr("DLY: "); txhex(i);
		txstr(" ");     txhex(_hin->hin_ctrl);
		txstr(" ");     txhex(_hin->hin_syncdata);
		txstr(" ");     txhex(_hin->hin_quality);
		sync_mask <<= 1;
		if ((_hin->hin_quality & 0x80000000) == 0) {
			txstr("  No synch");
			sync_mask |= 1;
		}
		txstr("\r\n");
	}

	sync_mask = zip_bitrev(sync_mask);
	sync_mask ^= -1;
	for(int i=0; i<31; i++) {
		if (((sync_mask>>i) & 7)==7) {
			txstr("\r\nSetting delay to ");
			v = 0x80000000|(i+1);
			_hin->hin_ctrl = v;
			txhex(v); txstr("\r\n");
			break;
		}
	}
	zip_halt();
#endif
}
