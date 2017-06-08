////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rdsync.cpp
//
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
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

#include "port.h"
#include "regdefs.h"
#include "ttybus.h"

FPGA	*m_fpga;

void	usage(void) {
	printf("USAGE: rdsync\n");
}

#define	NV	16
int main(int argc, char **argv) {
#if	defined(R_HDMI_INCLK) && (R_HIN_SYNC_CTRL)
	FPGAOPEN(m_fpga);
	unsigned	buf[NV], nc, raww, rawh, w, h;
	double	pixclk_hz, framerate_hz, linerate_hz;

	if (argc != 1) {
		usage();
		exit(EXIT_FAILURE);
	}

	// printclk(m_fpga, R_SYSCLK,      "System");
	// printclk(m_fpga, R_HDMI_OUTCLK, "HCLKOUT");
	nc = m_fpga->readio(R_HDMI_INCLK);
	pixclk_hz = nc;
	m_fpga->readi(R_HIN_SYNC_CTRL, NV, buf);

	w = buf[8] & 0x0ffff;
	h = buf[9] & 0x0ffff;
	raww = (buf[8] >> 16) & 0x0ffff;
	rawh = (buf[9] >> 16) & 0x0ffff;

	for(int i=0; i<NV; i++) {
		printf("RD[%04x = %04x] = %08x\n", i*4+R_HIN_SYNC_CTRL, i, buf[i]);
	}
	printf("Display    :  %4dx%3d\n", w, h);
	printf("Raw size   :  %4dx%3d\n", raww, rawh);

	framerate_hz = pixclk_hz / (raww*rawh);
	printf("Pixel Clock: %6.2f MHz\n", pixclk_hz    / 1.e6);
	if (raww > 0) {
		linerate_hz  = pixclk_hz / (raww);
		printf("Line Rate  : %6.2f kHz\n", linerate_hz  / 1.e3);
		if (rawh > 0) {
			printf("Frame Rate : %6.2f  Hz\n", framerate_hz);
		}
	}

 // 148.50 1920 2008 2052 2200 1080 1084 1089 1125 +hsync +vsync 
	printf("ModeLine   : %6.2f ", pixclk_hz/1.e6);
	printf("%d %d %d %d ", w, (buf[10]>>16)&0x0ffff,
		(buf[10]&0x0ffff), raww);
	printf("%d %d %d %d ", h,
		(buf[11]>>16)&0x0ffff, (buf[11]&0x0ffff), rawh);
	printf("\n");

	delete	m_fpga;
#else
	printf("No HDMI synchronization compiled into the repo\n");
#endif
}

