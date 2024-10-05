////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/exregs.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To give a user access, via a command line program, to read
//		and write wishbone registers one at a time.  Thus this program
//	accesses the readio() and writeio() methods from devbus, but nothing
//	more.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
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
// }}}
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
#include "devbus.h"

DEVBUS	*m_fpga;
const	char	*gbl_fpgahost = FPGAHOST;
int		gbl_fpgaport = FPGAPORT;
bool		gbl_uart = true;

void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	for(int k=0; k<16; k++) {
		unsigned	newv, sword, fps;

		newv = k & 0x1f;
		newv = (newv << 8) | (newv << 16) | (newv << 24);
		m_fpga->writeio(R_FPS, newv);
		sleep(4);
		fps   = m_fpga->readio(R_FPS);
		sword = m_fpga->readio(R_SYNCWORD);
		printf("%2d, %02x: %08x, %08x\n", k, k, fps, sword);
	}

	delete	m_fpga;
}

