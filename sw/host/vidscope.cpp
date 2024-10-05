////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/vidscope.cpp
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
// Copyright (C) 2022-2024, Gisselquist Technology, LLC
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

#ifndef	R_VIDSCOPE
int main(int argc, char **argv) {
	printf("This design was not built with the VIDEO scope within it.\n");
	exit(EXIT_FAILURE);
}
#else

#define	WBSCOPE		R_VIDSCOPE
#define	WBSCOPEDATA	R_VIDSCOPED

DEVBUS	*m_fpga;
void	closeup(int v) {
	m_fpga->kill();
	exit(0);
}

class	VIDSCOPE : public SCOPE {
public:
	unsigned VMODE = 6;

	VIDSCOPE(DEVBUS *fpga, unsigned addr, unsigned fps, bool vecread = true)
		: SCOPE(fpga, addr, false, vecread) {
		VMODE = (fps >> 29) & 7;
	};
	~VIDSCOPE(void) {}
	virtual	void	decode(DEVBUS::BUSW val) const {
	}

	virtual	void	define_traces(void) {
		switch(VMODE) {
		case 0: // SRC DEBUG
			register_trace("FRAME_LAST", 1, 30);
			register_trace("RX_VALID",   1, 27);
			register_trace("RX_READY",   1, 26);
			register_trace("RX_HLAST",   1, 25);
			register_trace("RX_VLAST",   1, 24);
			register_trace("RX_DATA",   24, 0);
			break;
		case 1: // ALPHA DEBUG
			register_trace("FRAME_LAST", 1, 30);
			register_trace("ALPHA",        2, 28);
			register_trace("ALPH_VALID",   1, 27);
			register_trace("ALPH_READY",   1, 26);
			register_trace("ALPH_HLAST",   1, 25);
			register_trace("ALPH_VLAST",   1, 24);
			register_trace("ALPH_DATA",   24, 0);
			break;
		case 2: // PIPELINE DEBUG
			register_trace("FRAME_LAST",  1, 30);
			register_trace("PIPE_VALID",  1, 27);
			register_trace("PIPE_READY",  1, 26);
			register_trace("PIPE_HLAST",  1, 25);
			register_trace("PIPE_VLAST",  1, 24);
			register_trace("PIPE_DATA",  24, 0);
			break;
		case 3: // TRANSMIT
			// register_trace("FRAME_LAST", 1, 30);
			// register_trace("OUT_VALID",  1, 27);
			// register_trace("OUT_READY",  1, 26);
			// register_trace("OUT_HLAST",  1, 25);
			// register_trace("OUT_VLAST",  1, 24);
			// register_trace("OUT_DATA",  24,  0);

			register_trace("di_valid",  1, 23);
			register_trace("di_ready",  1, 22);
			// register_trace("di_hdr",  24,  0);
			register_trace("di_last",  1, 20);
			register_trace("di_data",  8, 12);

			register_trace("opkt_valid", 1, 11);
			register_trace("opkt_ready", 1, 10);
			register_trace("opkt_hdr",   1,  9);
			register_trace("opkt_last",  1,  8);
			register_trace("opkt_data",  8,  0);
			break;
		case 4: // Data Island debug
			// register_trace("DI_DATA", 32, 0);

			register_trace("dis_valid",    1, 30);
			register_trace("dis_ready",    1, 29);
			register_trace("dis_last",     1, 28);
			register_trace("dis_data",     7, 21);
			//
			register_trace("pktdec_valid", 1, 20);
			register_trace("pktdec_last",  1, 19);
			register_trace("pktdec_data",  8, 18);
			//
			register_trace("ipkt_valid",   1, 10);
			register_trace("ipkt_hdr",     1,  9);
			register_trace("ipkt_last",    1,  8);
			register_trace("ipkt_data",    8,  0);

			break;
		/*
		case 5: // RAW Data Island debug
			register_trace("OPKT_VALID",   1, 31);
			register_trace("DI_VALID",     1, 30);
			register_trace("DI_LAST",      1, 29);
			register_trace("DI_DATA",      8, 21);
			register_trace("PKTDEC_VALID", 1, 20);
			register_trace("PKTDEC_LAST",  1, 19);
			register_trace("PKTDEC_DATA",  8, 11);
			register_trace("IPKT_VALID",   1, 10);
			register_trace("IPKT_HDR",     1,  9);
			register_trace("IPKT_LAST",    1,  8);
			register_trace("IPKT_DATA",    8,  0);
			break;
		*/
		case 5: // Raw input capture
			register_trace("iBLUE",  10, 20);
			register_trace("iGREEN", 10, 10);
			register_trace("iRED",   10,  0);
			break;
		case 6: // (CLR=GREEN) HDMI decoding debug
			// register_trace("trigger", 32, 0);
			// register_trace("sync_valid",       1, 30);
			// register_trace("chosen_match_loc", 4, 26);
			// register_trace("match_loc",        4, 22);
			// register_trace("sync",            10, 12);
			// register_trace("valid_match",      1, 11);
			// register_trace("any_sync",         1, 10);
			// register_trace("i_px",            10, 0);

			// register_trace("control_sync",   1,30);
			// register_trace("vid_start_red",  1,29);
			// register_trace("vid_start_grn",  1,28);
			// register_trace("vid_start_blu",  1,27);
			// register_trace("pix_valid",      1,26);
			// register_trace("o_vsync",        1,25);
			// register_trace("o_hsync",        1,24);
			// register_trace("dbg_red",        8,16);
			// register_trace("dbg_grn",        8, 8);
			// register_trace("dbg_blu",        8, 0);

// 0x40
// 0x80
// 0x80
// 0x3D
// DATA: 0x00,0x00,0x00,0x00,0x00....,
//			0x01, 0x10, 0x01, 0x10, 0x11, 0x00, 0x11, 0x00

			register_trace("pix_valid",   1,28);
			register_trace("o_vsync",     1,27);
			register_trace("o_hsync",     1,26);
			register_trace("sgrn_aux5",   1,25);
			register_trace("sred_aux5",   1,24);
			register_trace("sgrn_aux",    4,20);
			register_trace("sred_aux",    4,16);
			register_trace("sblu_aux",    5,11);
			register_trace("M_DI_VALID",  1,10);
			register_trace("M_DI_HDR",    1, 9);
			register_trace("M_DI_LAST",   1, 8);
			register_trace("M_DI_DATA",   8, 0);

			break;
		default:
			break;
		}
	}
};

int main(int argc, char **argv) {
	m_fpga = connect_devbus(NULL);

	signal(SIGSTOP, closeup);
	signal(SIGHUP, closeup);

	unsigned fps = m_fpga->readio(R_FPS);

	VIDSCOPE *scope = new VIDSCOPE(m_fpga, WBSCOPE, fps);
	scope->set_clkfreq_hz(100000000);
	if (!scope->ready()) {
		printf("Scope is not yet ready:\n");
		scope->decode_control();
	} else {
		scope->print();
		scope->writevcd("vidscope.vcd");
	}
	delete	m_fpga;
}
#endif
