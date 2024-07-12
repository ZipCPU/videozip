////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/netstat.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Reads the network PHY's registers through it's MDIO interface
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>
// }}}

#include "regdefs.h"
#include "port.h"
#include "exbus.h"
#include "design.h"

DEVBUS	*m_fpga;

void	usage(void) {
	printf("USAGE: netstat\n");
	printf("\tNo arguments required or accepted.\n\n");
	printf(
	"\tnetstat will attempt to connect to the FPGA and read and decode\n"
	"\tthe NETRX and NETTX registers from the ethernet controller.  The\n"
	"\tdecoded register values will be placed onto the standard output\n"
	"\tstream.\n\n");
}

#ifndef	R_MEGANET_TXCMD
#define	NO_NETWORK_CONTROLLER
#endif
#ifndef	R_MEGANET_RXCMD
#define	NO_NETWORK_CONTROLLER
#endif

int main(int argc, char **argv) {
#ifdef	NO_NETWORK_CONTROLLER
	printf(
"This program depends upon the NETTX/NETRX interface from the network\n"
"controller.  This interface was not built into your design.  Please add it\n"
"in and try again.\n");
#else

	m_fpga = connect_devbus(NULL);

	if (argc != 1) {
		// usage();
		printf("USAGE: netstat\n");
		exit(-1);
	}

	unsigned	v;

	////////////////////////////////
	//
	v = m_fpga->readio(R_MEGANET_RXCMD);
	if ((v & 0xc0000000) == 0)
		printf("RX:\t1000 Mbase T\n");
	else if ((v & 0xc0000000) == 0x40000000)
		printf("RX:\t 100 Mbase T\n");
	else if ((v & 0xc0000000) == 0x80000000)
		printf("RX:\t  10 Mbase T\n");
	else
		printf("RX:\tUnknown speed\n");
	if (v & 0x20000000)
		printf("RX:\tHalf duplex\n");
	else
		printf("RX:\tFull duplex\n");
	if (v & 0x10000000)
		printf("RX:\tlink is down\n");
	else
		printf("RX:\tlink is up\n");
	
	////////////////////////////////
	//
	v = m_fpga->readio(R_MEGANET_TXCMD);
	if ((v & 0xc0000000) == 0)
		printf("TX:\t1000 Mbase T\n");
	else if ((v & 0xc0000000) == 0x40000000)
		printf("TX:\t 100 Mbase T\n");
	else if ((v & 0xc0000000) == 0x80000000)
		printf("TX:\t  10 Mbase T\n");
	else
		printf("TX:\tUnknown speed\n");
	if (v & 0x0080000)
		printf("TX:\tHardware IP check  -- DISABLED\n");
	if (v & 0x0040000)
		printf("TX:\tNETWORK IS IN RESET\n");
	if (v & 0x0020000)
		printf("TX:\tHardware MAC check -- DISABLED\n");
	if (v & 0x0010000)
		printf("TX:\tHardware CRC check -- DISABLED\n");

	////////////////////////////////
	//
	v = m_fpga->readio(R_MEGANET_MACHI);
	printf("MAC: %02x:%02x", (v>>8)&0x0ff, (v & 0x0ff));
	v = m_fpga->readio(R_MEGANET_MACLO);
	printf(":%02x:%02x:%02x:%02x\n",
		(v>>24)&0x0ff, ((v>>16) & 0x0ff), (v>>8)&0x0ff, (v & 0x0ff));

	v = m_fpga->readio(R_MEGANET_MACHI);
	printf("MAC: %02x:%02x", (v>>8)&0x0ff, (v & 0x0ff));
	v = m_fpga->readio(R_MEGANET_MACLO);
	printf(":%02x:%02x:%02x:%02x\n",
		(v>>24)&0x0ff, ((v>>16) & 0x0ff), (v>>8)&0x0ff, (v & 0x0ff));

	v = m_fpga->readio(R_MEGANET_IPADDR);
	printf("IP: %3d.%3d.%3d.%3d\n",
		(v>>24)&0x0ff, (v>>16)&0x0ff, (v>> 8)&0x0ff, (v    )&0x0ff);

	// v = m_fpga->readio(R_NET_RXMISS);
	// printf("%6d\tMissed packets\n", v);
	// v = m_fpga->readio(R_NET_RXERR);
	// printf("%6d\tPackets received in error\n", v);
	// v = m_fpga->readio(R_NET_RXCRC);
	// printf("%6d\tPackets with bad CRCs\n", v);

	delete	m_fpga;
#endif
}
