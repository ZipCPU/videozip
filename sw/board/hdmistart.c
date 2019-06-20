////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	hdmistart.c
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This file is a part of trying to start up an HDMI port.
//		Specifically, the program within it will
//
//	1. Make sure the HPA (HDMI sink) is de-asserted
//	2. Wait for HPD (HDMI source) to be asserted
//	3. Copy any EDID data from the HDMI source port I2C master to the
//		I2C slave on the HDMI sink port.
//	4. Enable/assert the HDMI sink (HPA) GPIO wire.
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

#if	defined(_BOARD_HAS_HDMI_SRC_EDID) && defined(HDMIIN_ACCESS)
#else
#define	NO_HDMI_PORT
#endif

void entry(void) {
#ifdef	NO_HDMI_PORT
	txstr("No HDMI port within this repository\n");
#else
	unsigned	v;
	int		valid_edid = 0;

	txstr("\n\nHDMISTART\n\n");
	txstr("De-asserting the HDMI detect flag on the HDMI sink\n");
	v = GPIO_HDMI_IN_HPA_CLR
		| GPIO_HDMI_IN_ENB_CLR
		| GPIO_HDMI_OUT_EN_CLR;
	txstr("Setting GPIO to "); txhex(v); txstr("\n");
	*_gpio = v;

	if (0 == (*_gpio & GPIO_HDMI_OUT_DETECT)) {
		int	cnt = 0;
		txstr("No HDMI output (monitor) detected.\n");
		txstr("Waiting until one is plugged in.\n");
		while(0 == (*_gpio & GPIO_HDMI_OUT_DETECT)) {
			wait_ms(10);
			if (cnt++ > 100) {
				txstr(" -- Still waiting\n");
				cnt = 0;
			}
		}
	}

	txstr("HDMI output (monitor) detected.\n");
	txstr("Attempting to read EDID.\n");
	_edout->o_spd = 1000;

	do {
		for(int i=0; i<4; i++) {
			_edout->o_cmd = READ_EDID((i<<6),(1<<6));
			wait_while_edout_busy();

			if (_edout->o_cmd & EDID_SRC_ERR) {
				txstr("EDID-ERR detected, aborting\n");
				zip_halt();
			}
		}

		// Check the EDID CRC
		if ((_edout->o_data[0] == 0x00ffffff)
			&&(_edout->o_data[1] == 0xffffff00)) {
			valid_edid = 1;
		} else if ((_edout->o_data[0] == 0)
			&&(_edout->o_data[1] == 0)) {
			valid_edid = 0;
			wait_ms(200);
		} else {
			txstr("Invalid EDID-SRC data: 0x");
			txhex(_edout->o_data[0]);
			txstr(" : 0x");
			txhex(_edout->o_data[1]);
			txstr("\n");

			zip_halt();
		}
	} while(valid_edid == 0);

	txstr("Copying the EDID to the HDMI sink port\n");

	for(int i=0; i<256/4; i++)
		_edin[i] = _edout->o_data[i];

	txstr("Enabling the HDMI sink port\n");
	v = GPIO_HDMI_IN_HPA_SET
		| GPIO_HDMI_IN_ENB_SET;
	txstr("Setting GPIO to "); txhex(v); txstr("\n");
	*_gpio = GPIO_HDMI_IN_HPA_SET
		| GPIO_HDMI_IN_ENB_SET;
	txstr("Enabling the HDMI source port\n");
	v = GPIO_HDMI_OUT_EN_SET;
	txstr("Setting GPIO to "); txhex(v); txstr("\n");
	*_gpio = GPIO_HDMI_OUT_EN_SET;
	txstr("\n\n* * All done! * *\n");
	zip_halt();
#endif
}
