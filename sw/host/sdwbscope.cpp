////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/sdwbscope.cpp
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
#include <design.h>
#include "devbus.h"
#include "scopecls.h"

#ifndef	R_SDWBSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with an SDIO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_SDWBSCOPE
#define	WBSCOPEDATA	R_SDWBSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	SDWBSCOPE : public SCOPE {
public:
	SDWBSCOPE(DEVBUS *fpga, unsigned addr, bool vecread = true)
		: SCOPE(fpga, addr, true, vecread) {};
	~SDWBSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
	}

	virtual	void	define_traces(void) {
		//
		register_trace("w_card_busy",    1,30);
		register_trace("o_cmd_request",  1,29);
		register_trace("i_cmd_busy",     1,28);
		register_trace("i_cmd_done",     1,27);
		register_trace("i_cmd_err",      1,26);
		register_trace("i_cmd_ercode",   2,24);
		register_trace("i_cmd_response", 1,23);
		//
		register_trace("i_dma_busy",     1,22);
		register_trace("i_dma_err",      1,21);
		register_trace("o_dma_abort",    1,20);
		register_trace("o_dma_sd2s",     1,19);
		register_trace("o_sd2s_valid",   1,18);
		register_trace("i_sd2s_ready",   1,17);
		register_trace("o_sd2s_last",    1,16);
		register_trace("o_dma_s2sd",     1,15);
		register_trace("i_s2sd_valid",   1,14);
		register_trace("o_s2sd_ready",   1,13);
		//
		register_trace("o_tx_mem_valid", 1,12);
		register_trace("i_tx_mem_ready", 1,11);
		register_trace("o_tx_mem_last",  1,10);
		register_trace("o_tx_en",        1, 9);
		register_trace("r_tx_request",   1, 8);
		register_trace("i_tx_done",      1, 7);
		register_trace("i_tx_err",       1, 6);
		//
		register_trace("i_rx_mem_valid", 1, 5);
		register_trace("i_rx_done",      1, 4);
		register_trace("i_rx_err",       1, 3);
		register_trace("i_x_ecode",      1, 2);
		register_trace("r_rx_request",   1, 1);
		register_trace("o_rx_en",        1, 0);

		// Bonus/double use
		//	Not typically enabled.  These make long collects
		//	harder.
		// register_trace("dbl_rxvalid",    1, 19);
		// register_trace("dbl_rxdata",     4, 15);
		// register_trace("dbl_txvalid",    1,  4);
		// register_trace("dbl_txdata",     4,  0);
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	SDWBSCOPE *scope = new SDWBSCOPE(m_fpga, WBSCOPE);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("sdwbscope.vcd");
	}
	delete	m_fpga;
}
#endif
