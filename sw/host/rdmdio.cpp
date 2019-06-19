////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rdmdio.cpp
//
// Project:	OpenArty, an entirely open SoC based upon the Arty platform
//
// Purpose:	Reads and decodes the complete network control (MDIO, or
//		management data input/output) interface.
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
#include "design.h"

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

void	usage(void) {
	printf("USAGE: netsetup\n");
}

int main(int argc, char **argv) {
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	if ((argc < 1)||(argc > 2)) {
		// usage();
		printf("USAGE: netsetup\n");
		exit(-1);
	}

#ifndef	NETCTRL_ACCESS
	printf(
"This program depends upon the MDIO interface.  This interface was not\n"
"built into your design.  Please add it in and try again.\n");
#else
	unsigned	v;
	v = m_fpga->readio(R_MDIO_BMCR);
	printf("    BMCR    %04x\tBasic Mode Control Register\n", v);
	if (v & 0x08000)
		printf("                \tReset in progress\n");
	if (v & 0x04000)
		printf("                \tLoopback enabled\n");
	if (v & 0x01000)
		printf("                \tAuto-negotiation enabled\n");
	else if ((v & 0x04)==0) {
		printf("                \tAuto-negotiation disabled\n");
		if (v & 0x02000)
		printf("                \t100Mb/s -- manual selection\n");
		else
		printf("                \t 10Mb/s -- manual selection\n");
	} // else the speed decoding is reserved
	if (v & 0x00800)
		printf("                \tPHY is powered down\n");
	if (v & 0x00400)
		printf("                \tPort is isolated from MII\n");
	if (v & 0x00200)
		printf("                \tRestart-auto-negotiation\n");
	if ((v& 0x00100)==0)
		printf("                \tHalf-duplex mode\n");
	if (v & 0x00080)
		printf("                \tCollision test enabled\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_BMSR);
	printf("R/O BMSR    %04x\tBasic Mode Status Register\n", v);
	if (v & 0x08000)
		printf("                \t100Base-T4 capable\n");
	if (v & 0x04000)
		printf("                \t100Base-TX Full Duplex capable\n");
	if (v & 0x02000)
		printf("                \t100Base-TX Half Duplex capable\n");
	if (v & 0x01000)
		printf("                \t 10Base-TX Full Duplex capable\n");
	if (v & 0x00800)
		printf("                \t 10Base-TX Half Duplex capable\n");
	if (v & 0x00400)
		printf("                \t 10Base-T2 Full Duplex capable\n");
	if (v & 0x00200)
		printf("                \t 10Base-T2 Half Duplex capable\n");
	if (v & 0x00100)
		printf("                \t1000Base-T Device suports ESR register 0x0f\n");
	// 0x080 -- reserved
	if (v & 0x00040)
		printf("                \tPreamble suppression capable\n");
	if (v & 0x00020)
		printf("                \tAuto-negotiation complete\n");
	if (v & 0x00010)
		printf("                \tRemote fault detected\n");
	if (v & 0x00008)
		printf("                \tDevice is capable of auto-negotiation\n");
	if (v & 0x00004)
		printf("                \tLink is up\n");
	if (v & 0x00002)
		printf("                \tJabber condition detected (10Mb/s mode)\n");
	if (v & 0x00001)
		printf("                \tExtended register capabilities\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PHYIDR1);
	printf("R/O PHYID1  %04x\tPHY Identifier Reg #1\n", v);
	//printf("            %4x\tOUI MSB\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PHYIDR2);
	printf("R/O PHYID2  %04x\tPHY Identifier Reg #2\n", v);
	printf("            %4x\tOUI LSBs\n", (v>>10)&0x3f);
	printf("            %4x\tVendor model number\n",   (v>>4)&0x3f);
	printf("            %4x\tModel revision number\n", v&0x0f);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_ANAR);
	printf("    ANAR    %04x\tAuto-negotiation advertisement register\n", v);
	if (v & 0x8000)
		printf("                \tNext pages exchange desired\n");
	if (v & 0x2000)
		printf("                \tRemote fault detected\n");
	if (v & 0x0800)
		printf("                \tAdvertise assymetric pause capability\n");
	if (v & 0x0400)
		printf("                \tAdvertise pause frame capability\n");
	if (v & 0x0200)
		printf("                \t100-Base T4 support\n");
	if (v & 0x0100)
		printf("                \tAdvertise support for 100Base TX full-duplex\n");
	if (v & 0x0080)
		printf("                \tAdvertise support for 100Base TX half-duplex\n");
	if (v & 0x0040)
		printf("                \tAdvertise support for  10Base TX full-duplex\n");
	if (v & 0x0020)
		printf("                \tAdvertise support for  10Base TX half-duplex\n");
	printf("            %4x\tSelector field\n", v&0x01f);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_ANLPAR);
	printf("    ANLPAR  %04x\tAuto-negotiation link partner ability\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_ANER);
	printf("    ANER    %04x\tAuto-negotiation expansion register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_ANNPTR);
	printf("    ANNPTR  %04x\tAuto-negotiation Next page TX\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_GBCR);
	printf("      GBCR  %04x\t1000Base-T Control Register\n", v);
	if ((v&0xe000)==0x2000)
		printf("                \tTest mode 1 - Transmit Jitter test\n");
	else if ((v&0xe000)==0x4000)
		printf("                \tTest mode 2 - Transmit Jitter test (MASTER mode)\n");
	else if ((v&0xe000)==0x6000)
		printf("                \tTest mode 3 - Transmit Jitter test (SLAVE mode)\n");
	else if ((v&0xe000)==0x8000)
		printf("                \tTest mode 4 - Transmit Distortion test\n");
	else if ((v&0xe000)!=0)
		printf("                \tTest mode (Reserved!)\n");
	if (v&0x1000) {
		if (v & 0x0800)
		printf("                \tManual MASTER configuration\n");
		else
		printf("                \tManual SLAVE configuration\n");
	}

	if (v&0x0400)
		printf("                \tPrefer multi-port device (MASTER)\n");
	else
		printf("                \tPrefer single-port device (SLAVE)\n");
	if (v&0x0200)
		printf("                \tAdvertise 1000Base-T Full-duplex capability\n");


	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_GBSR);
	printf("R/O   GBSR   %04x\t1000Base-T Status Register\n", v);
	if (v & 0x8000)
		printf("                \tMASTER/SLAVE configuration fault detected\n");
	if (v & 0x4000)
		printf("                \tLocal PHY configuration resolved to MASTER\n");
	else
		printf("                \tLocal PHY configuration resolved to SLAVE\n");
	if ((v & 0x2000)==0)
		printf("                \tLocal Receiver Status: NOT OKAY\n");
	if ((v & 0x1000)==0)
		printf("                \tRemote Receiver Status: NOT OKAY\n");
	if (v & 0x0800)
		printf("                \tLink partner is     capable of 1000Base-T full-duplex\n");
	else
		printf("                \tLink partner is NOT capable of 1000Base-T full-duplex\n");
	if (v & 0x0400)
		printf("                \tLink partner is     capable of 1000Base-T half-duplex\n");
	else
		printf("                \tLink partner is NOT capable of 1000Base-T half-duplex\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_MACR);
	printf("W/O   MACR  %04x\tMMD Access Control Register\n", v);
	if ((v&0xc000)==0x0)
		printf("                \tAddress\n");
	else if ((v&0xc000)==0x4000)
		printf("                \tData with no increment\n");
	else if ((v&0xc000)==0x8000)
		printf("                \tData with post increment on reads and writes\n");
	else if ((v&0xc000)==0xc000)
		printf("                \tData with post increment on writes only\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_MAADR);
	printf("     MAADR  %04x\tMMD Access Address Data Register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_GBESR);
	printf("R/O  GBESR  %04x\t1000Base-T Extended Status Register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PHYCR);
	printf("     PHYCR  %04x\tPHY specific control register\n", v);
	if (v&0x8000)
		printf("                \tRX clock output disabled\n");
	if (v&0x0800)
		printf("                \tAssert CRS on transmit (GMII)\n");
	if (v&0x0400)
		printf("                \tForce link good\n");
	if (v&0x0040)
		printf("                \tEnable Auto-crossover mechanism\n");
	if (v&0x0010)
		printf("                \tCLK125 remains at logic low\n");
	if (v&0x0001)
		printf("                \tDisable jabber function\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PHYSR);
	printf("R/O  PHYSR  %04x\tPHY specific status register\n", v);
	if ((v&0xc000)==0)
		printf("                \t  10Mbps link speed\n");
	else if ((v&0xc000)==0x4000)
		printf("                \t 100Mbps link speed\n");
	else if ((v&0xc000)==0x8000)
		printf("                \t1000Mbps link speed\n");
	else
		printf("                \t(Reserved) link speed ??\n");
	if (v&0x2000)
		printf("                \tFull duplex mode\n");
	else
		printf("                \tHalf duplex mode\n");
	if (v&0x1000)
		printf("                \tNew page received\n");
	if ((v&0x0800)==0)
		printf("                \tSpeed and duplex mode not yet resolved\n");
	if ((v&0x0400)==0)
		printf("                \tLink is NOT okay\n");
	if (v&0x0040)
		printf("                \tMDI Crossover\n");
	if ((v&0x0002)==0)
		printf("                \tReceiver is NOT OK\n");
	if (v&0x0001)
		printf("                \tJabber indication\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_INER);
	printf("      INER  %04x\tInterrupt Enable Register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_INSR);
	printf("R/O   INSR  %04x\tInterrupt Status Register\n", v);
	if (v & 0x8000)
		printf("                \tAuto-Negotiation Error\n");
	if (v & 0x1000)
		printf("                \tPage received\n");
	if ((v & 0x0800)==0)
		printf("                \tAuto-Negotiation not complete\n");
	if (v & 0x0400)
		printf("                \tLink status changed\n");
	if (v & 0x0200)
		printf("                \tSymbol Error detected\n");
	if (v & 0x0100)
		printf("                \tFalse Carrier\n");
	if (v & 0x0001)
		printf("                \tJabber detected\n");

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_RXERC);
	printf("R/O RXERC   %04x\tReceive Error Counter\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_LDPSR);
	printf("R/O LPDSR   %04x\tLink Down Power Saving Register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_EPAGSR);
	printf("   EPAGSR   %04x\tExtension Page Select Register\n", v);

	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PAGSEL);
	printf("   PAGSEL   %04x\tPage Select Register\n", v);

/*
	////////////////////////////////////////
	v = m_fpga->readio(R_MDIO_PC1R);
	printf("     PC1R   %04x\tPSC Control 1 Register, MMD Device 3\n", v);
*/

	delete	m_fpga;
#endif
}
