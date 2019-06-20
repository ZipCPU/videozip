////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	edidtxscope.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To communicate with a generic scope, specifically the one for
//		testing the I2C communication path associated with an EDID
//	data set.  Further, this file defines what the various wires are
//	on that path, as well as the fact that the scope is compressed.
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
#include "scopecls.h"
#include "ttybus.h"

#if	defined(R_EDID_SCOPC) && defined(R_EDID_SCOPD)
#else
#define	NO_SCOPE
#endif

#define	WBSCOPE		R_EDID_SCOPC
#define	WBSCOPEDATA	R_EDID_SCOPD

FPGA	*m_fpga;

class	EDIDTXSCOPE : public SCOPE {
public:
	EDIDTXSCOPE(FPGA *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, true, vecread) {};
	~EDIDTXSCOPE(void) {}

	virtual	void	define_traces(void) {
		register_trace("ll_cyc",       1, 30);
		register_trace("ll_stb",       1, 29);
		//
		register_trace("last_adr",     7, 22);
		register_trace("wr_inc",       1, 21);
		register_trace("count_left",   6, 15);
		register_trace("watchdog",     1, 14);
		//
		register_trace("o_ack",        1, 13);
		register_trace("o_busy",       1, 12);
		//
		register_trace("o_err",        1, 11);
		register_trace("stop_bit",     1, 10);
		register_trace("start_bit",    1,  9);
		register_trace("channel_busy", 1,  8);
		//
		register_trace("ll_state", 4, 4);
		//
		register_trace("i_tx_scl", 1, 3);
		register_trace("i_tx_sda", 1, 2);
		register_trace("o_tx_scl", 1, 1);
		register_trace("o_tx_sda", 1, 0);
	}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	i_tx_sck, i_tx_sda, o_tx_sck, o_tx_sda, ll_state,
			ll_cyc, ll_stb, ll_stall, ll_ack, ll_err;

		ll_cyc   = (val>>30)&1;
		ll_stb   = (val>>29)&1;
		ll_ack   = (val>>13)&1;
		ll_stall = (val>>12)&1;
		ll_err   = (val>>11)&1;
		//
		ll_state = (val>> 4)&15;
		//
		i_tx_sck = (val>>3)&1;
		i_tx_sda = (val>>2)&1;
		o_tx_sck = (val>>1)&1;
		o_tx_sda = (val   )&1;
		//

		printf("%s%s %s%s%s sLL[%x] TX-CMD[%s %s] TX-RCVD[%s %s]",
			(ll_cyc) ? "CYC":"   ",
			(ll_stb) ? "STB":"   ",
			(ll_ack) ? "ACK":"   ",
			(ll_stall)?"STALL":"     ",
			(ll_err) ? "ERR":"   ",
			ll_state,
			(o_tx_sck)?"SCK":"   ", (o_tx_sda)?"SDA":"   ",
			(i_tx_sck)?"SCK":"   ", (i_tx_sda)?"SDA":"   ");
	}
};

int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("Design was not build with any EDID-TX scope within it\n");
#else
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	FPGAOPEN(m_fpga);

	// Here, we open a scope.  An EDIDTXSCOPE specifically.  The difference
	// between an EDIDTXSCOPE and any other scope is ... that the
	// EDIDTXSCOPE has particular things wired to particular bits, whereas
	// a generic scope ... just has data.  Well, that and the EDIDTXSCOPE
	// is a compressed scope, whereas a generic scope could be either.
	EDIDTXSCOPE *scope = new EDIDTXSCOPE(m_fpga, WBSCOPE);

	if (!scope->ready()) {
		// If we get here, then ... nothing started the scope.
		// It either hasn't primed, hasn't triggered, or hasn't finished
		// recording yet.  Trying to read data would do nothing but
		// read garbage, so we don't try.
		printf("Scope is not yet ready: (%08x->%08x)\n", WBSCOPE, m_fpga->readio(WBSCOPE));
		scope->decode_control();
	} else {
		// The scope has been primed, triggered, the holdoff wait 
		// period has passed, and the scope has now stopped.
		//
		// Hence we can read from our scope the values we need.
		scope->print();
		// If we want, we can also write out a VCD file with the data
		// we just read.
		scope->writevcd("edid.vcd");
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
#endif
}
