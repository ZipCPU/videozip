////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/excheck.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is just a quick program to check whether or not the ExBus
//		compression works correctly as advertised.  Specifically, we're
//	testing the table compression--not the address, ack, or read repeat
//	compressions.  Table compression allows you to describe a value based
//	upon how long its been since it was last seen.  It's used in two place:
//	first, when writing to the device, and second when reading from the
//	device.  A value written twice will first enter the table, and then
//	be referenced on the second write to spare bandwidth.
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
#include <stdint.h>

#include "regdefs.h"
#include "port.h"
#include "devbus.h"

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

bool	isvalue(const char *v) {
	// {{{
	const char *ptr = v;

	while(isspace(*ptr))
		ptr++;

	if ((*ptr == '+')||(*ptr == '-'))
		ptr++;
	if (*ptr == '+')
		ptr++;
	if (*ptr == '0') {
		ptr++;
		if (tolower(*ptr) == 'x')
			ptr++;
	}

	return (isdigit(*ptr));
}
// }}}

const	char	*gbl_fpgahost = FPGAHOST;
int		gbl_fpgaport = FPGAPORT;
bool		gbl_uart = true;

// #define	MEM_ADDR	R_BKRAM
#define	MEM_ADDR	R_SDRAM

int main(int argc, char **argv) {
	const	unsigned NLEN = 768;
	char	*videozip_env;
	int	opt;
	uint32_t	*testbuf, *checkbuf, *ovbuf;
	bool	passed = true;

	// Check first for our environment value -- use it to set defaults
	// {{{
	if (NULL != (videozip_env = getenv(gbl_devname)) && videozip_env[0]) {
		char	*portstr, *host = NULL;

		videozip_env = strdup(videozip_env);
		if (0 == strncasecmp(videozip_env, "UART://", 7)) {
			host = videozip_env+7;
			gbl_uart = true;
		} else if (0 == strncasecmp(videozip_env, "EXBUS://", 8)) {
			host = videozip_env+8;
			gbl_uart = true;
		} else if (0 == strncasecmp(videozip_env, "SIM://", 6)) {
			host = videozip_env+6;
			gbl_uart = true;
		} else if (0 == strncasecmp(videozip_env, "NEXBUS://", 9)) {
			host = videozip_env+6;
			gbl_uart = false;
		} else if (0 == strncasecmp(videozip_env, "NET://", 6)) {
			host = videozip_env+6;
			gbl_uart = false;
		} else if (0 == strncasecmp(videozip_env, "UDP://", 6)) {
			host = videozip_env+6;
			gbl_uart = false;
		} else {
			fprintf(stderr, "ERR: Unrecognized environment string\n");
			exit(EXIT_FAILURE);
		}

		gbl_fpgaport = gbl_uart ? UARTDBGPORT : UDP_DBGPORT;
		portstr = strchr(host, ':');
		if (portstr) {
			*portstr++ = '\0';
			if (*portstr && isdigit(*portstr))
				gbl_fpgaport = atoi(portstr);
		} if (host)
			gbl_fpgahost = host;
fprintf(stderr, "Connecting to %s://%s:%d\n", gbl_uart ? "UART":"NET",
gbl_fpgahost, gbl_fpgaport);
	}
	// }}}

	// Process all arguments, save the address and optional value
	// {{{
	while(-1 != (opt=getopt(argc, argv, "dn:p:m:"))) {
		switch(opt) {
		// case 'h': usage(); exit(EXIT_SUCCESS); break;
		case 'n': gbl_fpgahost = strdup(optarg); break;
		case 'p': gbl_fpgaport = strtoul(optarg, NULL, 0); break;
		default: // usage();
			exit(EXIT_FAILURE);
			break;
		}
	}
	// }}}

	{
		char	comstr[256];
		sprintf(comstr, "%s://%s:%d", gbl_uart ? "UART":"NET",gbl_fpgahost, gbl_fpgaport);
		m_fpga = connect_devbus(comstr);
	}

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	// Set up some random, and non-repeating values
	// {{{
	testbuf  = new uint32_t[NLEN];
	checkbuf = new uint32_t[NLEN*2];
	ovbuf    = new uint32_t[NLEN*2];
	for(unsigned k=0; k<NLEN; k++) {
		bool	dup;

		do {
			dup = false;

			testbuf[k] = rand();
			if ((k & 0x07)==0)
				testbuf[k] &= ~0x0ff;
			else if (0 == (k & 0x3f))
				testbuf[k] &= ~0x07fff;
			for(unsigned j=0; j<k; j++) {
				if (testbuf[k] == testbuf[j]) {
					dup = true;
					break;
				}
			}
		} while(dup);
	}
	// }}}

	for(unsigned offset=0; (offset<NLEN) && passed; offset++) {
		// {{{
		printf("Read check, testing offset  %d\n", offset);

		// Write this data to the device
		printf("\tWRITE"); fflush(stdout);
		m_fpga->writei(MEM_ADDR, NLEN, testbuf);
		// Write it again, this time with an offset
		printf(", WRITE"); fflush(stdout);
		m_fpga->writei(MEM_ADDR + 4*offset, NLEN, testbuf);
		// Now, read both back
		printf(", READ"); fflush(stdout);
		m_fpga->readi(MEM_ADDR, NLEN + offset, checkbuf);
		// ... and compare the result
		printf(", CHECK\n"); fflush(stdout);
		for(unsigned k=0; k<offset; k++) {
			if (checkbuf[k] != testbuf[k]) {
				printf("RD-ERR: @0x%08x -- CHECK[%d]=%08x != 0x%08x (expected)\n", MEM_ADDR + k, k, checkbuf[k], testbuf[k]);
				passed = false;
			}
		} for(unsigned k=0; k<NLEN; k++) {
			if (checkbuf[offset+k] != testbuf[k]) {
				printf("RD-ERR: @0x%08x -- CHECK[%d+%d]=%08x != 0x%08x (expected)\n", MEM_ADDR + offset + k, offset, k, checkbuf[offset+k], testbuf[k]);
				passed = false;
			}
		}
	}
	// }}}

	for(unsigned offset=0; (offset<NLEN) && passed; offset++) {
		// {{{
		printf("Write check, testing offset  %d\n", offset);
		for(unsigned k=0; k<offset; k++)
			ovbuf[k] = testbuf[k];
		for(unsigned k=0; k<NLEN; k++)
			ovbuf[offset+k] = testbuf[k];

		printf("\tWRITE"); fflush(stdout);
		m_fpga->writei(MEM_ADDR, NLEN + offset, ovbuf);
		// Now, read both back
		printf(", READ"); fflush(stdout);
		m_fpga->readi(MEM_ADDR, NLEN + offset, checkbuf);
		// ... and compare the result
		printf(", CHECK\n"); fflush(stdout);
		for(unsigned k=0; k<NLEN+offset; k++) {
			if (checkbuf[k] != ovbuf[k]) {
				printf("WR-ERR: CHECK[%d+%d]=%08x != 0x%08x (expected)\n", offset, k, checkbuf[k], ovbuf[k]);
				passed = false;
			}
		}
	}
	// }}}

	if (passed)
		m_fpga->writei(MEM_ADDR, NLEN, testbuf);
	for(unsigned offset=0; (offset + 8 < NLEN) && passed; offset++) {
		// {{{
		printf("Address check, testing offset  %d\n", offset);

		// Now, read both back
		printf("\tREAD"); fflush(stdout);
		m_fpga->readi(MEM_ADDR, 2, checkbuf);
		printf(", READ"); fflush(stdout);
		m_fpga->readi(MEM_ADDR + 4*offset, 8, &checkbuf[2]);
		// ... and compare the result
		printf(", CHECK\n"); fflush(stdout);
		for(unsigned k=0; k<2; k++) {
			if (checkbuf[k] != testbuf[k]) {
				printf("AD-ERR: CHECK[%d+%d]=%08x != 0x%08x (expected)\n", offset, k, checkbuf[k], testbuf[k]);
				passed = false;
			}
		} for(unsigned k=0; k<8; k++) {
			if (checkbuf[2+k] != testbuf[k+offset]) {
				printf("AD-ERR: CHECK[%d+%d]=%08x != 0x%08x (expected)\n", offset, k+2, checkbuf[2+k], testbuf[k+offset]);
				passed = false;
			}
		}
	}
	// }}}

	if (passed) printf("SUCCESS!\n");

	if (m_fpga->poll())
		printf("FPGA was interrupted\n");
	delete	m_fpga;
}

