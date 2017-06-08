////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tmdscope.cpp
//
// Project:	
//
// Purpose:	To communicate with the scope that collects samples from the
//		HDMI input wires.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2015-2017, Gisselquist Technology, LLC
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

#if	defined(R_SCOP_HDMIIN_CTRL) && defined(R_SCOP_HDMIIN_DATA)
#else
#define	NO_SCOPE
#endif

#define	WBSCOPE		R_SCOP_HDMIIN_CTRL
#define	WBSCOPEDATA	R_SCOP_HDMIIN_DATA

#define	BREV_PIXEL

FPGA	*m_fpga;

unsigned	brev_pixel(unsigned v) {
	unsigned r = 0;
	for(int i=0; i<10; i++) {
		r = (r<<1) | (v&1);
		v >>= 1;
	} return r;
}

bool	issync(unsigned pix) {
	if (pix == 0x0354)
		return true;
	else if (pix == 0x0ab)
		return true;
	else if (pix == 0x0154)
		return true;
	else if (pix == 0x02ab)
		return true;
	return false;
}

class	TMDSCOPE : public SCOPE {
public:
	TMDSCOPE(FPGA *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, false, vecread) {};
	~TMDSCOPE(void) {}

	virtual	void	define_traces(void) {
		register_trace("hsync",   1, 31);
		register_trace("vsync",   1, 30);
		register_trace("pvr",     1, 29);
		register_trace("pvg",     1, 28);
		register_trace("dpixg5",  1, 27);
		register_trace("dpixg0",  1, 26);
		register_trace("syncd_b",10, 16);
		register_trace("encoding_failure",  1, 15);
		register_trace("vguard_found",      1, 14);
		register_trace("vguard_ever_found", 1, 13);
		register_trace("vguard_valid",      1, 12);
		register_trace("vguard_now",        1, 11);
		register_trace("pre_vguard",        2,  9);
		register_trace("pvb",               1,  8 );
		register_trace("dpix_b",            8,  0);
	}

	static void decode_tmds(unsigned v) {
		unsigned px = v;


	//
		if (px == 0x354)
			printf("S0.0");
		else if (px == 0x0ab)
			printf("S0.1");
		else if (px == 0x154)
			printf("S1.0");
		else if (px == 0x2ab)
			printf("S1.1");
		//
		else if (px == 0x29c)
			printf("Th.0");
		else if (px == 0x263)
			printf("Th.1");
		else if (px == 0x2e4)
			printf("Th.2");
		else if (px == 0x2e2)
			printf("Th.3");
		//
		else if (px == 0x171)
			printf("Th.4");
		else if (px == 0x11e)
			printf("Th.5");
		else if (px == 0x18e)
			printf("Th.6");
		else if (px == 0x13c)
			printf("Th.7");
		//
		else if (px == 0x2cc)
			printf("Th.8");
		else if (px == 0x139)
			printf("Th.9");
		else if (px == 0x19c)
			printf("Th.a");
		else if (px == 0x26c)
			printf("Th.b");
		//
		else if (px == 0x28e)
			printf("Th.c");
		else if (px == 0x271)
			printf("Th.d");
		else if (px == 0x163)
			printf("Th.e");
		else if (px == 0x2c3)
			printf("Th.f");
		else {
			if (v&0x200) {
				v ^= 0x0ff;
			}

			unsigned r = 0;
			r = (v & 0x0ff) ^ (v<<1);
			r &= 0x0ff;
			if (v&0x0100)
				r ^= 0x0fe;
			printf("  %02x", r);
		}

	}

	virtual	void	decode(DEVBUS::BUSW val) const {
		int	hsync, vsync, pvr, pvb, syncd_b,
			vguard_now, pre_vguard, dpix_b, b;
		int	dpixr5, dpixr0, dpixg5, dpixg0, state, pixvalid;

		hsync   = (val >> 31)&1;
		vsync   = (val >> 30)&1;
		pixvalid= (val >> 29)&1;
		pvr     = (val >> 28)&1;
		state   = (val >> 26)&3;
		syncd_b = (val >> 16) & 0x03ff;
		vguard_now  = (val >> 15)&1;
		pre_vguard  = (val >> 13)&3;
		dpixr5      = (val >> 12)&1;
		dpixr0      = (val >> 11)&1;
		dpixg5      = (val >> 10)&1;
		dpixg0      = (val >>  9)&1;
		pvb         = (val >>  8)&1;
		dpix_b      = (val     )&0x0ff;
		//

		b = brev_pixel(syncd_b);

		switch(state) {
		case 0: printf("- CTL-  "); break;
		case 1: printf(" (ISL)  "); break;
		case 2: printf("**VID** "); break;
		case 3: printf("invalid "); break;
		default: break;
		}

		printf("%s%s %s[%s?%s] [(%d%d,%d%d,x)->%d %s], %03x -> %02x -- > ",
			(vsync) ? "V":" ",
			(hsync) ? "H":" ",
			(pixvalid)?"V":" ",
			(pvr) ? "R":" ",
			(pvb) ? "B":" ",
			dpixr5,dpixr0,dpixg5, dpixg0,
			(pre_vguard),
			(vguard_now)?"N":" ",
			syncd_b, dpix_b);
			//
			decode_tmds(b);
	}
};

#define	DEFAULT_HLENGTH	2200
int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("No TMDS scope defined\n");
#else
	int	hlength = DEFAULT_HLENGTH;
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	FPGAOPEN(m_fpga);

	// Here, we open a scope.  An TMDSCOPE specifically.  The difference
	// between an TMDSCOPE and any other scope is ... that the
	// TMDSCOPE has particular things wired to particular bits, whereas
	// a generic scope ... just has data.
	TMDSCOPE *scope = new TMDSCOPE(m_fpga, WBSCOPE);

	if (!scope->ready()) {
		// If we get here, then ... nothing started the scope.
		// It either hasn't primed, hasn't triggered, or hasn't finished
		// recording yet.  Trying to read data would do nothing but
		// read garbage, so we don't try.
		printf("Scope is not yet ready: (%08x->%08x)\n",
			WBSCOPE, m_fpga->readio(WBSCOPE));
		scope->decode_control();
	} else {
		// The scope has been primed, triggered, the holdoff wait 
		// period has passed, and the scope has now stopped.
		//
		// Hence we can read from our scope the values we need.
		scope->print();
		// If we want, we can also write out a VCD file with the data
		// we just read.
		scope->writevcd("rawgreen.vcd");


		for(int i=0; i<hlength; i++) {
			bool	is_match;
			unsigned	b, v, match_v;

			printf("%4d: ", i);
			for(int j=0; (j*hlength+i)<scope->scoplen(); j++) {

				v = (*scope)[j*hlength+i];

				if (j == 0) {
					is_match = true;
					match_v = v;
				} else if (is_match) {
					if (v != match_v)
						is_match = false;
				}
				printf("%08x ", v);
			}

			{
				v = (*scope)[i];

				b = (v >> 16)&0x03ff;

				b = brev_pixel(b);

				int	hsync, vsync, pvr, pvb, pxvalid,
					vguard_now, vstate;
				hsync = (v >> 31)&1;
				vsync = (v >> 30)&1;
				pxvalid=(v >> 29)&1;
				pvr   = (v >> 28)&1;
				vstate= (v >> 26)&3;
				vguard_now  = (v >> 15)&1;
				pvb   = (v >>  8)&1;
				// gsync = (issync(b))?1:0;

				if (pxvalid) {
					printf("PX");
				} else	printf("  ");
				printf("[%s.%s]", (pvr)?"R":" ", (pvb)?"B":" ");

				printf("%s%s%s",
					(vsync)?"V":" ",
					(hsync)?"H":" ",
					(vsync|hsync)?"-SYNC":"     ");
					
				printf("(%03x->%02x)", b, (v&0x0ff));
				printf(" %d%s", vstate, (vguard_now)?" VidG":"     ");
				if (is_match) 	printf(" MATCH ");
				else		printf("       ");
				TMDSCOPE::decode_tmds(b);
			}
			printf("\n");
		}
	}

	// Now, we're all done.  Let's be nice to our interface and shut it
	// down gracefully, rather than letting the O/S do it in ... whatever
	// manner it chooses.
	delete	m_fpga;
#endif
}
