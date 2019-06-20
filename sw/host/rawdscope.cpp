////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	rawdscope.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To communicate with the scope that collects samples from the
//		HDMI input wires.
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

class	RAWDSCOPE : public SCOPE {
public:
	RAWDSCOPE(FPGA *fpga, unsigned addr, bool vecread=true)
		: SCOPE(fpga, addr, false, vecread) {};
	~RAWDSCOPE(void) {}

	virtual	void	define_traces(void) {
		register_trace("hsync",  1, 31);
		register_trace("vsync",  1, 30);
		register_trace("red",   10, 20);
		register_trace("green", 10, 10);
		register_trace("blue",  10,  0);
	}

	void decode_tmds(unsigned v) const {
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
		int	r, g, b, hsync, vsync;

		hsync = (val>>31)&1;
		vsync  = (val>>30)&1;
		r = (val>>20)&0x03ff;
		g = (val>>10)&0x03ff;
		b = (val    )&0x03ff;

#ifdef	BREV_PIXEL
		r = brev_pixel(r);
		g = brev_pixel(g);
		b = brev_pixel(b);
#endif

		printf("%s%s %03x : %03x : %03x -- >",
			(vsync)?"V":" ",
			(hsync)?"H":" ",
			r, g, b);

		if ((b==0x2cc)&&(g == 0x0133)&&(r == 0x2cc))
			printf("Video Guard Band");
		else if ((g == 0x0133)&&(r == 0x0133))
			printf("Data Island Guard Band");
		else {
			//
			decode_tmds(r); printf(" ");
			decode_tmds(g); printf(" ");
			decode_tmds(b);
		}
	}
};

#define	DEFAULT_HLENGTH	2200
int main(int argc, char **argv) {
#ifdef	NO_SCOPE
	printf("The design was not built with any raw HDMI data capture within it\n");
#else
	int	hlength = DEFAULT_HLENGTH;
	// Open and connect to our FPGA.  This macro needs to be defined in the
	// include files above.
	FPGAOPEN(m_fpga);

	// Here, we open a scope.  An RAWDSCOPE specifically.  The difference
	// between an RAWDSCOPE and any other scope is ... that the
	// RAWDSCOPE has particular things wired to particular bits, whereas
	// a generic scope ... just has data.
	RAWDSCOPE *scope = new RAWDSCOPE(m_fpga, WBSCOPE);

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
		scope->writevcd("rawtmds.vcd");


		for(int i=0; i<hlength; i++) {
			bool	is_match;
			unsigned	r, g, b, v, match_r, match_g, match_b,
				hsync, vsync;

			printf("%4d: ", i);
			for(int j=0; (j*hlength+i)<scope->scoplen(); j++) {

				v = (*scope)[j*hlength+i];

				hsync = (v>>31)&1;
				vsync = (v>>30)&1;
				r = (v>>20)&0x03ff;
				g = (v>>10)&0x03ff;
				b = (v    )&0x03ff;

#ifdef	BREV_PIXEL
				r = brev_pixel(r);
				g = brev_pixel(g);
				b = brev_pixel(b);
#endif

				if (j == 0) {
					is_match = true;
					match_r = r;
					match_g = g;
					match_b = b;
				} else if (is_match) {
					if (r != match_r)
						is_match = false;
					else if (g != match_g)
						is_match = false;
					else if (b != match_b)
						is_match = false;
				}
				printf("%s%s%03x:%03x:%03x  ",
					(vsync)?"V":" ",
					(hsync)?"H":" ",
					r, g, b);
			}

			if (is_match) {
				v = (*scope)[i];

				r = (v>>20)&0x03ff;
				g = (v>>10)&0x03ff;
				b = (v    )&0x03ff;

#ifdef	BREV_PIXEL
				r = brev_pixel(r);
				g = brev_pixel(g);
				b = brev_pixel(b);
#endif

				bool	rsync, gsync; // , bsync;
				rsync = issync(r);
				gsync = issync(g);
				// bsync = issync(b);

				if (b == 0x0354)
					printf("IDLE");
				else if (b == 0x00ab)
					printf("HSYN");
				else if (b == 0x0154)
					printf("VSYN");
				else if (b == 0x02ab)
					printf("HV.S");
				else
					printf("%s%s  ",
						(rsync)?"R":" ",
						(gsync)?"G":" ");

				if((r == 0x02cc)&&(g == 0x0133)&&(b == 0x02cc))
					printf("VidG");
				else if ((r == 0x0133)&&(g == 0x0133))
					printf("DI.G");
				printf(" MATCH");
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
