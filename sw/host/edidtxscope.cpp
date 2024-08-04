////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/edidtxscope.cpp
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

#if	defined(R_EDID_SCOPC) && defined(R_EDID_SCOPD)
#else
#define	NO_SCOPE
#endif

#define	WBSCOPE		R_EDID_SCOPC
#define	WBSCOPEDATA	R_EDID_SCOPD

DEVBUS	*m_fpga;

class	EDIDTXSCOPE : public SCOPE {
public:
	EDIDTXSCOPE(DEVBUS *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, true, vecread) {};
	~EDIDTXSCOPE(void) {}

	virtual	void	define_traces(void) {
		//
		register_trace("ovw_valid",         1, 30);
		register_trace("i2c_abort",         1, 29);
		register_trace("i2c_stretch",       1, 28);
		register_trace("half_insn",         4, 24);
		register_trace("r_wait",            1, 23);
		register_trace("soft_halt_request", 1, 22);
		//
		register_trace("r_aborted",  1, 21);
		register_trace("r_err",      1, 20);
		register_trace("r_halted",   1, 19);
		register_trace("insn_valid", 1, 18);
		register_trace("half_valid", 1, 17);
		register_trace("imm_cycle",  1, 16);
		//
		register_trace("o_i2c_scl",  1, 15);
		register_trace("o_i2c_sda",  1, 14);
		register_trace("i_i2c_scl",  1, 13);
		register_trace("i_i2c_sda",  1, 12);
		register_trace("i2cinsn",   12,  0);
	}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	o_scl, o_sda, i_scl, i_sda, insn;

		o_scl = (val >> 15)&1;
		o_sda = (val >> 12)&1;
		i_scl = (val >> 13)&1;
		i_sda = (val >> 12)&1;
		insn  = val & 0x03ff;

		printf("%3s %3s / %03x",
				(o_scl && i_scl) ? "SCL" : "   ",
				(o_sda && i_sda) ? "SDA" : "   ",
				insn);
	}
};

int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("Design was not build with any EDID-TX scope within it\n");
#else
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	m_fpga = connect_devbus(NULL);

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
