////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rdclocks.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To read the three clock values off of the board, while also
//		turning the clock speed to something readable.
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

void	printclk(FPGA *fpga, unsigned addr, const char *name) {
	unsigned	nc;
	nc = m_fpga->readio(addr);
	printf("%12s: 0x%08x %10d %8.2f MHz\n", name, nc, nc, (double)(nc/1.e6));
}

void	usage(void) {
	printf("USAGE: rdclocks\n");
}

int main(int argc, char **argv) {
	FPGAOPEN(m_fpga);

	if (argc != 1) {
		usage();
		exit(EXIT_FAILURE);
	}

	printclk(m_fpga, R_SYSCLK,      "System");
	printclk(m_fpga, R_HDMI_INCLK,  "HCLKIN");
	printclk(m_fpga, R_HDMI_OUTCLK, "HCLKOUT");

	delete	m_fpga;
}

