////////////////////////////////////////////////////////////////////////////////
//
// Filename:	cpedid.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Debugging.  This program allows you to read the EDID information
//		from the source HDMI link, and write it out to a binary file
//	which can then be read by Linux EDID utilities
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
#include "byteswap.h"

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

void	usage(void) {
	printf("USAGE: cpedid\n"
"\n"
"\tReads the HDMI source port\'s EDID information and writes it to a file.\n"
"\n");
}

int main(int argc, char **argv) {
#ifdef	R_EDID_OUT
	int	skp=0;

	skp=1;
	for(int argn=0; argn<argc-skp; argn++) {
		if (argv[argn+skp][0] == '-') {
			usage();
			exit(EXIT_SUCCESS);
			skp++; argn--;
		} else
			argv[argn] = argv[argn+skp];
	} argc -= skp;

	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	char	edid_buffer[256];
	m_fpga->readi(R_EDID_OUT, (256>>2), (unsigned *)edid_buffer);
	byteswapbuf((256>>2), (unsigned *)edid_buffer);

	{
		FILE	*fp;

		fp = fopen("edidsrc.bin","w");
		fwrite(edid_buffer, 1, 256, fp);
		fclose(fp);
	}

	delete	m_fpga;
#else
	printf("Design has no sink EDID port\n");
#endif
}

