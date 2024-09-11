////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/hdmistart.c
// {{{
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
// }}}
// Copyright (C) 2017-2024, Gisselquist Technology, LLC
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
#include <stdint.h>
#include <design.h>
#include "board.h"
#include "zipcpu.h"
#include "zipsys.h"
#include "txfns.h"
#include "getedid.c"
// }}}

#include <stdio.h>
#include "i2c.c"

// #define	_BOARD_HAS_EDIDSCOPE
#ifdef	_BOARD_HAS_EDIDSCOPE

#define	EDIDSCOPE_SET		_edidscope->s_ctrl = WBSCOPE_DISABLE
#define	EDIDSCOPE_TRIGGER	_edidscope->s_ctrl = WBSCOPE_TRIGGER|WBSCOPE_DISABLE

#else

// #error "No scope"
#define	EDIDSCOPE_SET
#define	EDIDSCOPE_TRIGGER

#endif

/*
void	wait_ms(int ms) {
	constexpr	int	CLOCKS_PER_MS = CLKFREQHZ / 1000;

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
*/

#ifdef	_BOARD_HAS_VIDPIPE
#else
#define	NO_HDMI_PORT
#endif

int
main(int argc, char ** argv) {
#ifdef	NO_HDMI_PORT
	txstr("No HDMI port within this repository\n");
#else
	unsigned	v, vidcfg;
	int		valid_edid = 0;

	// Select 16b pixels (internally)
	//	external video source
	//	HDMI clock (comes externally)
	vidcfg = VIDCMAP_16CLR | VIDPIPE_RXCLOCK | VIDPIPE_RXSRC;
	_hdmi->v_control = vidcfg | VIDPIPE_RESET;

	EDIDSCOPE_SET;
	*_spio = 0x0ff00;

	txstr("+--------------------------------------+\n"
		"|             HDMI Startup             |\n"
		"+--------------------------------------+\n");

	txstr("\n"
		"De-asserting the upstream HDMI detect flag, and the\n"
		"downstream TX enable\n");

	v = GPIO_HDMIRX_HPA_CLR | GPIO_HDMIRX_TXEN_CLR;
	txstr("Setting GPIO to "); txhex(v); txstr("\n");
	*_gpio = v;

	// Wait for 200ms or so
	_zip->z_tmb = 20000000;
	while(_zip->z_tmb)
		;

	*_spio = 0x0ff00;	// Turn off all LEDs
	while(0 == (*_gpio & GPIO_HDMITX_DETECT)) {
		while(0 == (*_gpio & GPIO_HDMITX_DETECT))
			;

		// Wait for another 200ms or so
		_zip->z_tmb = 20000000;
		while(_zip->z_tmb)
			;
	}

	printf("GPIO now equal to %08x\n", *_gpio);

	*_spio = 0x0101;

	// Read EDID
	// {{{
	txstr("HDMI output (monitor) detected.\n");
	txstr("Attempting to read EDID, via @0x");
		txhex((unsigned)get_edid_script); txstr("\n");

	printf("Initial dump:\n");
		i2c_dump((I2CCPU * const)_edid);
		txstr("\n\n");

	i2c_clear((I2CCPU * const)_edid);
	printf("Next dump:\n");
		i2c_dump((I2CCPU * const)_edid);
		txstr("\n\n");

	_edid->ic_address = (unsigned)get_edid_script;

	_zip->z_tmc = 1000000;	// 10ms
	while(_zip->z_tmc != 0)
		;
	EDIDSCOPE_TRIGGER;

	while(0 == (_edid->ic_control & I2CC_STOPPED)) {
		if (_zip->z_tmc == 0) {
			printf("Timeout dump:\n");
			i2c_dump((I2CCPU * const)_edid);
			// Repeat every 4 seconds
			_zip->z_tmc = 4 * 100 * 1000 * 1000;
		}

		if (_edid->ic_control & I2CC_FAULT) {
			_edid->ic_control = I2CC_ABORT | I2CC_ERROR | I2CC_HALT;
			EDIDSCOPE_TRIGGER;
			txstr("Halting on I2CC Fault\n");
			while(0 == (_edid->ic_control & I2CC_STOPPED))
				;
		}
	}
	// }}}

	*_spio = 0x0302;

	// DUMP the EDID
	// {{{
	txstr("EDID:\n  0x");
	for(int k=0; k<256; k++) {
		unsigned	v, hx;

		v = _edidslv[k];
		// txstr("0x");

		// Upper
		// {{{
		hx = (v >> 4) & 0x0f;
		if (hx >= 10)
			txchr(hx - 10 + 'A');
		else
			txchr(hx + '0');
		// }}}

		// Lower
		// {{{
		hx = v & 0x0f;
		if (hx >= 10)
			txchr(hx - 10 + 'A');
		else
			txchr(hx + '0');
		// }}}

		if (k == 255)
			txchr('\n');
		else if (0x0f == (k & 0x0f))
			txstr("\n  0x");
		else if (7 == (k & 0x7))
			txstr("  ");
		else
			txchr(' ');
	}
	// }}}

	if (I2CC_FAULT & _edid->ic_control) {
		txstr("EDID Read fault\n");
		i2c_dump((I2CCPU * const)_edid);
		zip_halt();
	}

	// Validate the EDID data
	// {{{
	{
		int	failed = 0;

		if (0x00 != _edidslv[0]) failed = 1;
		if (0xff != _edidslv[1]) failed = 1;
		if (0xff != _edidslv[2]) failed = 1;
		if (0xff != _edidslv[3]) failed = 1;
		if (0xff != _edidslv[4]) failed = 1;
		if (0xff != _edidslv[5]) failed = 1;
		if (0xff != _edidslv[6]) failed = 1;
		if (0x00 != _edidslv[7]) failed = 1;

		if (!failed) {
			// Check the checksum
			unsigned	sum;
			for(int k=0; k<128; k++) {
				sum = sum + (_edidslv[k] & 0x0ff);
			} // txstr("CHECK SUM: "); txhex(sum); txstr("\n");
			if (0 != (sum & 0x0ff))
				failed = 1;
		}

		if (failed) {
			txstr("ERR: Invalid EDID\n");
			EDIDSCOPE_TRIGGER;
			i2c_dump((I2CCPU * const)_edid);
			zip_halt();
		}
	}
	// }}}

	// EDID is automatically forwarded

	// Assert the upstream hotplug, and enable the HDMI port--necessary
	// to get the HDMI clock.
	*_gpio = GPIO_HDMIRX_HPA_SET | GPIO_HDMIRX_TXEN_SET;
	_zip->z_tmb = 20;
	while(_zip->z_tmb)
		;
	_hdmi->v_control = vidcfg;	// Release the reset

	*_spio = 0x0f04;

	// Wait for the upstream video to be valid
	if (0 == (_hdmi->v_control & VIDPIPE_RXSYNCD)) {
		while(0 == (_hdmi->v_control & VIDPIPE_RXSYNCD)) {
			// Wait for 200ms or so
			_zip->z_tmb = 20000000;
			while(_zip->z_tmb)
				;

			*_spio = 0x0100 ^ (*_spio & 1);
		}

		_zip->z_tmb = 20000000;
		while(_zip->z_tmb)
			;
	}

	*_spio = 0x0707;

	txstr("\n\n* * All done! * *\n");
	zip_halt();

	return 0;
#endif
}
