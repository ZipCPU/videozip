////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	erxscope.cpp
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

class	ERXSCOPE : public SCOPE {
public:
	ERXSCOPE(FPGA *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, false, vecread) {};
	~ERXSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
		int	trigger, neop, macerr, bcast, clear, miss, rxerr,
			rxvalid, rxbusy, wr, npre, minv, crcv, crcd, crcerr,
			macv, dv, rxd;

		trigger= (val>>31)&1;
		neop   = (val>>30)&1;
		macerr = (val>>29)&1;
		bcast  = (val>>28)&1;
		clear  = (val>>27)&1;
		miss   = (val>>26)&1;
		rxerr  = (val>>25)&1;
		rxvalid= (val>>24)&1;
		rxbusy = (val>>23)&1;
		wr     = (val>>22)&1;
		npre   = (val>>21)&1;
		minv   = (val>>20)&1;
		crcv   = (val>>19)&1;
		crcd   = (val>>11)&0x0ff;
		crcerr = (val>>10)&1;
		macv   = (val>> 9)&1;
		dv     = (val>> 8)&1;
		rxd    = (val    )&0x0ff;

		printf("%s[%s%s%s%s%s%s%s%s%s%s%s%s%s]",
			(trigger)?"TR":"  ",
			(clear)?"CLR":"",
			(bcast)?"BC":"  ",
			//
			(rxbusy)?"BSY":"   ",
			(npre)?"P":" ",
			(macv)?"MAC":"   ",
			(minv)?"MN":"  ",
			(wr)?"WR":"  ",
			(neop)?"EOP":"   ",
			(rxvalid)?"VALID":"     ",
			//
			(macerr)?"MACER":"",
			(crcerr)?"CRCER":"",
			(rxerr)?"RXER":"",
			(miss)?"MISS":"");

		if (dv)
			printf("I:%02x ", rxd);
		else
			printf("%4s ","");

		if (crcv)
			printf("C:%02x", crcd);
		else
			printf("%4s","");
	}

	virtual	void	define_traces(void) {
		// trigger= (val>>31)&1;
		register_trace("EOP",1,30);
		register_trace("w_macerr",1,29);
		register_trace("w_broadcast",1,28);
		register_trace("n_rx_clear",1,27);
		register_trace("n_rx_miss",1,26);
		register_trace("n_rx_net_err",1,25);
		register_trace("n_rx_valid",1,24);
		register_trace("n_rx_busy",1,23);
		register_trace("w_rxwr",1,22);
		register_trace("w_npre",1,21);
		register_trace("w_rxmin",1,20);
		register_trace("w_rxcrc",1,19);
		register_trace("w_rxcrcd",8,11);
		register_trace("w_rxcrcerr",1,10);
		register_trace("w_rxmac",1,9);
		register_trace("i_net_rx_ctl",1,8);
		register_trace("i_net_rxd",8,0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_NETSCOPE
	printf("This design was not built with a NET scope within it.\n");
#else
	FPGAOPEN(m_fpga);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	ERXSCOPE *scope = new ERXSCOPE(m_fpga, WBSCOPE);
	// scope->set_clkfreq_hz(ENETCLKFREQHZ);
	scope->set_clkfreq_hz(125000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("erxscope.vcd");
	}
	delete	m_fpga;
#endif
}

