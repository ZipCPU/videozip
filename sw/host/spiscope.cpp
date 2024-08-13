////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/spiscope.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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

#include "design.h"
#include "regdefs.h"
#include "devbus.h"
#include "scopecls.h"

#define	WBSCOPE		R_SPISCOPE
#define	WBSCOPEDATA	R_SPISCOPED

#define	SCOPEBIT(VAL,B)	((val >> B)&1)

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SPISCOPE : public SCOPE {
public:
	SPISCOPE(DEVBUS *fpga, unsigned addr, bool vecread)
		: SCOPE(fpga, addr, false, false) {};
	~SPISCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
	}

	virtual	void define_traces(void) {
		register_trace("manual_mode",  1, 30);
		register_trace("imm_cycle",    1, 29);
		register_trace("r_stopped",    1, 28);
		register_trace("r_wait",       1, 27);
		register_trace("r_err",        1, 26);
		register_trace("dcd_stop",     1, 25);
		register_trace("dcd_valid",    1, 24);
		register_trace("dcd_ready",    1, 23);
		register_trace("dcd_active",   1, 22);
		register_trace("dcd_last",     1, 21);
		register_trace("dcd_send",     1, 20);
		register_trace("dcd_keep",     1, 19);
		register_trace("next_valid",   1, 18);
		register_trace("next_ready",   1, 17);
		//
		register_trace("next_illegal", 1, 16);
		register_trace("next_insn",    8,  8);
		//
		register_trace("o_csn",        1,  7);
		register_trace("o_sck",        1,  6);
		register_trace("o_mosi",       1,  5);
		register_trace("i_miso",       4,  0);
	}
};

int main(int argc, char **argv) {
#ifndef	R_SPISCOPE
	printf(
"This design was not built with an SPI scope attached.\n"
"\n"
"To use this design, create and enable the SPI controller, and the SPI scope\n"
"from that.  To do this, you'll need to adjust the file used by AutoFPGA\n"
"found in the auto-data/ directory, and then include it within the Makefile\n"
"of the same directory.\n");
#else
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SPISCOPE *scope = new SPISCOPE(m_fpga, WBSCOPE, true);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("spicpu.vcd");
	}
	delete	m_fpga;
#endif
}

