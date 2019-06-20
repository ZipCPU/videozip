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
// Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
#if	defined(R_SYSCLK) || defined(R_HDMI_CLK) || defined(R_HDMI_OUTCLK) ||defined(R_NETCLOCKCTR)
	FPGAOPEN(m_fpga);

	if (argc != 1) {
		usage();
		exit(EXIT_FAILURE);
	}

#ifdef	R_SYSCLK
	printclk(m_fpga, R_SYSCLK,      "System");
#endif
#ifdef	R_HDMI_INCLK
	printclk(m_fpga, R_HDMI_INCLK,  "HCLKIN");
#endif
#ifdef	R_HDMI_OUTCLK
	printclk(m_fpga, R_HDMI_OUTCLK, "HCLKOUT");
#endif
#ifdef	R_NETRXCLK
	printclk(m_fpga, R_NETRXCLK, "NETRXCK");
#endif
#ifdef	R_NETTXCLK
	printclk(m_fpga, R_NETTXCLK, "NETTXCK");
#endif
#ifdef	R_GENCLKFB
	printclk(m_fpga, R_GENCLKFB, "GENCLK ");
	{
		unsigned req, rv;
		double	ratio;
		bool	locked, enabled;

// True request is req<<2
// A value of 0x0800_0000 Should yield the input back
		rv   = m_fpga->readio(R_GENCLK);
		req  = rv & 0x3fffffff;
		ratio = (double)req * 1.0 / (double)(1<<29);
		locked  = (rv & 0x80000000);
		enabled = (rv & 0x40000000);
		printf("RV    = 0x%08x  %s%s\n", rv, (locked)?"LOCKED ":"",
			(enabled)?"":"(Disabled)");
		if (enabled) {
			printf("REQ   = 0x%08x\n", req);
			printf("Ratio = %11.6f\n", ratio);
			printf("Nominal request for 100 * 8 * 0x%08x / 2^28 = %11.6f\n", req,
				100.0 * ratio);
#ifdef	R_SYSCLK
			unsigned	nc;
			nc = m_fpga->readio(R_SYSCLK);
			printf("After adjusting for SYSCLK                 = %11.6f\n",
				nc * ratio / 1e6);
#endif
		}
	}
#endif

	delete	m_fpga;
#else
	printf("FPGA design was built without any clock measurement support\n");
#endif
}
