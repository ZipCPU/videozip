////////////////////////////////////////////////////////////////////////////////
//
// Filename:	readframe.cpp
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
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

void	usage(void) {
	printf("USAGE: readhist address\n");
}

int main(int argc, char **argv) {
	unsigned	address;

	if (argc != 2) {
		usage();
		exit(EXIT_FAILURE);
	}

	address = strtoul(argv[1], NULL, 0);

	FPGAOPEN(m_fpga);

	try {
		FILE	*fp;
		const	unsigned	NLOCS = 2200 * 70;
		unsigned data[NLOCS], rgbdata[NLOCS*3];
		const char	*FRAMEFILE = "framedata.32t";
		size_t		nw;

		m_fpga->readi(address, NLOCS, data);
		fp = fopen(FRAMEFILE, "w");
		if (!fp) {
			fprintf(stderr, "Could not open %s for writing\n", FRAMEFILE);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		for(unsigned i=0; i<NLOCS; i++) {
			if (data[i] & 0xc0000000)
				fprintf(stderr, "ERR: Data[%02d] = %08x\n", i, data[i]);
			rgbdata[i*3  ] = (data[i]>>20) & 0x03ff;
			rgbdata[i*3+1] = (data[i]>>10) & 0x03ff;
			rgbdata[i*3+2] = (data[i]    ) & 0x03ff;
		}

		nw = fwrite(rgbdata, sizeof(unsigned), NLOCS*3, fp);
		if (nw != NLOCS*3) {
			fprintf(stderr, "WARNING: Only %ld (out of %d) items written\n", nw, NLOCS);
		}

		fclose(fp);

	} catch(BUSERR b) {
		printf("%08x: BUS-ERROR\n", address);
	}

	delete	m_fpga;
}

