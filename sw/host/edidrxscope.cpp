////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/edidrxscope.cpp
// {{{
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
#include "scopecls.h"
#include "exbus.h"

#if	defined(R_EDIDSLVSCOPE) && defined(R_EDIDSLVSCOPED)
#else
#define	NO_SCOPE
#endif

#define	WBSCOPE		R_EDIDSLVSCOPE
#define	WBSCOPEDATA	R_EDIDSLVSCOPD

DEVBUS	*m_fpga;

class	EDIDRXSCOPE : public SCOPE {
public:
	EDIDRXSCOPE(DEVBUS *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, true, vecread) {};
	~EDIDRXSCOPE(void) {}

	virtual	void	define_traces(void) {
		//
		register_trace("i2c_start", 1, 29);
		register_trace("i2c_stop",  1, 28);
		//
		register_trace("wb_stb",    1, 27);
		register_trace("wb_we",     1, 26);
		register_trace("wb_stall",  1, 25);
		register_trace("wb_ack",    1, 24);
		register_trace("wb_addr",   6, 16);
		//
		register_trace("s_valid",   1, 15);
		register_trace("s_ready",   1, 14);
		register_trace("s_last",    1, 13);
		register_trace("s_data",    8,  4);
		//
		register_trace("i_i2c_scl", 1,  3);
		register_trace("i_i2c_sda", 1,  2);
		register_trace("o_i2c_scl", 1,  1);
		register_trace("o_i2c_sda", 1,  0);
	}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	o_scl, o_sda, i_scl, i_sda, s_valid, s_ready, s_last,
			s_data;

		s_valid = (val >> 15) & 1;
		s_ready = (val >> 14) & 1;
		s_last  = (val >> 13) & 1;
		s_data  = (val >>  4) & 0x0ff;
		i_scl   = (val >>  3) & 1;
		i_sda   = (val >>  2) & 1;
		o_scl   = (val >>  1) & 1;
		o_sda   = (val >>  0) & 1;

		printf("%3s %3s / %1s%1s %02x/%1s",
				(o_scl && i_scl) ? "SCL" : "   ",
				(o_sda && i_sda) ? "SDA" : "   ",
				s_valid ? "V":" ",
				s_ready ? "R":" ",
				s_data & 0x0ff,
				s_last ? "L":" ");
	}
};

int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("Design was not build with any EDID-RX scope within it\n");
#else
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	m_fpga = connect_devbus(NULL);

	// Here, we open a scope.  An EDIDRXSCOPE specifically.  The difference
	// between an EDIDRXSCOPE and any other scope is ... that the
	// EDIDRXSCOPE has particular things wired to particular bits, whereas
	// a generic scope ... just has data.  Well, that and the EDIDRXSCOPE
	// is a compressed scope, whereas a generic scope could be either.
	EDIDRXSCOPE *scope = new EDIDRXSCOPE(m_fpga, WBSCOPE);

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
		scope->writevcd("edidslv.vcd");
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
#endif
}
