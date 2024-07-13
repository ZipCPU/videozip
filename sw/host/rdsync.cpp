////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/rdsync.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
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
//
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "regdefs.h"
#include "port.h"
#include "exbus.h"

DEVBUS	*m_fpga;

void	usage(void) {
	printf("USAGE: rdsync\n");
}

#define	NV	32
int main(int argc, char **argv) {
#ifdef	R_HDMI
	unsigned	buf[NV], nc, raww, rawh, w, h;
	double	pixclk_hz, framerate_hz, linerate_hz;

	m_fpga = connect_devbus(NULL);

	if (argc != 1) {
		usage();
		exit(EXIT_FAILURE);
	}

	m_fpga->readi(R_HDMI, NV, buf);

	if (0 != buf[1] && 0 != buf[4]) { // Incoming video
		// {{{
		printf("Incoming video\n");
		printf("----------------\n");
		printf("  %12s: %9d Hz\n", "Pixel Clock", buf[1]);
		printf("  %12s: %9d x %5d\n", "Size", buf[4] & 0x0ffff,
			(buf[4] >> 16)&0x0ffff);
		printf("  %12s: %9d x %5d\n", "Porch", buf[5] & 0x0ffff,
			(buf[5] >> 16)&0x0ffff);
		printf("  %12s: %9d x %5d\n", "Synch", buf[6] & 0x0ffff,
			(buf[6] >> 16)&0x0ffff);
		printf("  %12s: %9d x %5d\n", "Raw Size", buf[7] & 0x0ffff,
			(buf[7] >> 16)&0x0ffff);
		printf("  %12s: Line Rate  : %6.2f kHz\n", "Line Rate",
			(double)buf[1] / (double)(buf[7] & 0x0ffff)/ 1.e3);
		printf("  %12s: %9f\n", "Frame rate", (double)buf[1]
			/ (double)((buf[7] & 0x0ffff)
				* ((buf[7] >> 16)&0x0ffff)));
		printf("  %12s : %6.2f ", "ModeLine", (double)buf[1]/1.e6);
		printf("%d %d %d %d ", (buf[4] &0x0ffff), buf[ 5] & 0x0ffff,
			(buf[ 6]&0x0ffff), (buf[7] & 0x0ffff));
		printf("%d %d %d %d ",
			(buf[4] >> 16)&0x0ffff, (buf[5]>>16)&0x0ffff,
			(buf[6] >> 16)&0x0ffff, (buf[7]>>16)&0x0ffff);
		printf("%shsync ", (buf[ 6] & 0x08000) ? "+":"-");
		printf("%svsync ",((buf[ 6] >> 31)&1) ? "+":"-");

		printf("\n");
		// }}}
	} if (0 != buf[1]) { // Sync control
		// {{{
		printf("Incoming sync control\n");
		printf("----------------\n");
		printf("  %12s: %9d\n", "Red Delay",   (buf[15] >> 24)&0x01f);
		printf("  %12s: %9d\n", "Green Delay", (buf[15] >> 16)&0x01f);
		printf("  %12s: %9d\n", "Blue Delay",  (buf[15] >>  8)&0x01f);
		printf("  %12s: %9d\n", "Sync Control", buf[24]);
		// }}}
	}

	if (0 != buf[3]) { // Outgoing video
		// {{{
		printf("Outgoing video\n");
		printf("----------------\n");
		printf("  %12s: %9d Hz\n", "Pixel Clock", buf[3]);
		printf("  %12s: %9d x %5d\n", "Size", buf[8] & 0x0ffff,
			(buf[8] >> 16)&0x0ffff);
		printf("  %12s: %9d x %5d\n", "Porch", buf[9] & 0x0ffff,
			(buf[9] >> 16)&0x0ffff);
		printf("  %12s: %9d x %5d\n", "Synch", buf[10] & 0x07fff,
			(buf[10] >> 16)&0x07fff);
		printf("  %12s: %9d x %5d\n", "Raw Size", buf[11] & 0x0ffff,
			(buf[11] >> 16)&0x0ffff);
		printf("  %12s: Line Rate  : %6.2f kHz\n", "Line Rate",
			(double)buf[3] / (double)(buf[11] & 0x0ffff)/ 1.e3);
		printf("  %12s: %9f Hz\n", "Frame rate", (double)buf[3]
			/ (double)((buf[11] & 0x0ffff)
				* ((buf[11] >> 16)&0x0ffff)));
		printf("  %12s : %6.2f ", "ModeLine", (double)buf[1]/1.e6);
		printf("%d %d %d %d ", (buf[4] &0x0ffff), buf[ 5] & 0x0ffff,
			(buf[ 6]&0x0ffff), (buf[7] & 0x0ffff));
		printf("%d %d %d %d ",
			(buf[ 8] >> 16)&0x0ffff, (buf[ 9]>>16)&0x0ffff,
			(buf[10] >> 16)&0x07fff, (buf[11]>>16)&0x0ffff);
		printf("%shsync ", (buf[10] & 0x08000) ? "+":"-");
		printf("%svsync ",((buf[10] >> 31)&1) ? "+":"-");
		printf("\n");
		// }}}
	}

	if (0 != buf[3] && 0 != buf[12]) { // Overlay info video
		// {{{
		printf("Overlay info\n");
		printf("----------------\n");
		printf("  %12s: %9d x %5d\n", "OvSize", buf[13] & 0x0ffff,
			(buf[13] >> 16)&0x0ffff);
		printf("  %12s: +%8d , +%4d\n", "OvOffset", buf[14] & 0x0ffff,
			(buf[14] >> 16)&0x0ffff);
		// }}}
	}

	for(int i=0; i<NV; i++) {
		printf("RD[%04x = %04x] = %08x\n", i*4+R_HDMI, i, buf[i]);
	}

 // 148.50 1920 2008 2052 2200 1080 1084 1089 1125 +hsync +vsync 
	printf("  %12s : %6.2f ", "ModeLine", (double)buf[1]/1.e6);
	printf("%d %d %d %d ", (buf[4] &0x0ffff), buf[ 5] & 0x0ffff,
		(buf[ 6]&0x0ffff), (buf[7] & 0x0ffff));
	printf("%d %d %d %d ",
		(buf[4] >> 16)&0x0ffff, (buf[5]>>16)&0x0ffff,
		(buf[6] >> 16)&0x07fff, (buf[7]>>16)&0x0ffff);
	printf("\n");

	delete	m_fpga;
#else
	printf("ERR: Design does not contain an HDMI video pipeline\n");
#endif
}

