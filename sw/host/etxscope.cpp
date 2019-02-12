////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	etxscope.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This file decodes the debug bits produced by the enetpackets.v
//		Verilog module, and stored in a Wishbone Scope.  It is useful
//	for determining if the packet transmitter works at all or not.
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
#include <design.h>
#include "regdefs.h"
#include "ttybus.h"
#include "scopecls.h"

#define	WBSCOPE		R_NETSCOPE
#define	WBSCOPEDATA	R_NETSCOPED

FPGA	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	ETXSCOPE : public SCOPE {
public:
	ETXSCOPE(FPGA *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, false, vecread) {};
	~ETXSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	txcmd, complete, txbusy, txden, txd,
			macen, paden, crcen, crcd, txctl, otx;

		txcmd   = (val>>31)&1;
		complete= (val>>30)&1;
		txbusy  = (val>>29)&1;
		txden   = (val>>28)&1;
		txd     = (val>>20)&0x0ff;
		macen   = (val>>19)&1;
		paden   = (val>>18)&1;
		crcen   = (val>>17)&1;
		crcd    = (val>> 9)&0x0ff;
		txctl   = (val>> 8)&1;
		otx     = (val>> 0)&0x0ff;

		printf("%s[%s%s]",
			(txcmd)?"TR":"  ",
			(complete)?"DONE":"    ",
			(txbusy)?"BUSY":"    ");

		if (txden)
			printf(" T[%02x]", txd);
		else
			printf("      ");

		printf(" %s%s",
			//
			(macen)?"MAC":"   ",
			(paden)?"P":" ");

		if (crcen)
			printf(" C[%02x]", crcd);
		else
			printf("      ");

		if (txctl)
			printf(" O[%02x]", otx);
		else
			printf("      ");
	}

	virtual	void	define_traces(void) {
		// trigger= (val>>31)&1;
		register_trace("n_tx_cmd",1,31);
		register_trace("n_tx_complete",1,30);
		register_trace("n_tx_busy",1,29);
		register_trace("r_txd_en",1,28);
		register_trace("r_txd",8,20);
		register_trace("w_macen",1,19);
		register_trace("w_paden",1,18);
		register_trace("w_txcrcen",1,17);
		register_trace("w_txcrcd",8,9);
		register_trace("o_net_tx_ctl",1,8);
		register_trace("o_net_txd",8,0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_NETSCOPE
	printf("This design was not built with a NET scope within it.\n");
#else
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	ETXSCOPE *scope = new ETXSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(125000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("etxscope.vcd");
	}
	delete	m_fpga;
#endif
}

