////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/memtest.c
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Used to determine if the DDR3 SDRAM controller is working or
//		not.  Contains a series of tests, applied across memory, for
//	this purpose.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
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
// }}}
#include "zipcpu.h"
#include "zipsys.h"
#include "board.h"
#include "txfns.h"

// extern	char	_sdram[0x40000000];

#define	SCOPE_DELAY	16

#define	STEP(F,T)  asm volatile("LSR 1,%0\n\tXOR.C %1,%0" : "+r"(F) : "r"(T))
#define	FAIL		asm("TRAP")

//
// memchk
// {{{
void	memchk(int *mem, int *end, unsigned seed) {
	int	counts = seed;
	// const	int	TAPS = 0x0485b5;
	// const	int	TAPS = 0x0110003;	// 2Gb
	// const	int	TAPS = 0x0280005;	// 4Gb
	const	int	TAPS = 0x0400015;	// 8Gb
	// const	int	TAPS = 0x0400019;	// 8Gb
	// const	int	TAPS = 0x0400043;	// 8Gb
	// const	int	TAPS = 0x0400051;	// 8Gb
	// const	int	TAPS = 0x04000c1;	// 8Gb
	// const	int	TAPS = 0x0400181;	// 8Gb
	// const	int	TAPS = 0x0400501;	// 8Gb
	// const	int	TAPS = 0x0401401;	// 8Gb
	// const	int	TAPS = 0x07fffdf;	// 8Gb
	char	*const cmem= (char *)mem;
	char	*const endc= (char *)end;
	unsigned	timestamps[9];

	for(int i=0; i<9; i++)
		timestamps[i] = 0;
	timestamps[0] = _zip->z_m.ac_ck;

	////////////////////////////////////////////////////////////////////////
	//
	// #1, data line check
	// {{{
	txchr('\n');
	for(int k=0; k<512; k++) {
		for(int j=0; j<512/8; j++) {
			if ((k>>3) == j)
				cmem[j] = (1<<(k&7));
			else
				cmem[j] = '\0';
		}

		for(int j=0; j<512/8; j++) {
			if ((k>>3) == j) {
				if (cmem[j] != (1<<(k&7)))
					FAIL;
			} else if (cmem[j] != '\0')
				FAIL;
		}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Clear the bottom 3 LED's
	*_spio = 0x0e00;
	// }}}
#endif
	timestamps[1] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #2, address line check
	// {{{
	txchr('1');
	for(int k=0; cmem + (1<<k)<endc; k++) {
		for(int j=0; cmem + (1<<j) < endc; j++) {
			if (k == j)
				cmem[j] = 0xad;
			else
				cmem[j] = '\0';
		}

		for(int j=0; cmem + (1<<j) < endc; j++) {
			if (k == j) {
				if (cmem[j] != 0xad)
					FAIL;
			} else if (cmem[j] != '\0')
				FAIL;
		}
	}

#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Clear the bottom 3 LED's
	*_spio = 0x0e02;
	// }}}
#endif
	timestamps[2] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #3, sequential access, filled with LRS
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('2');
	{
		int	*mptr = mem;
		unsigned fill;

		// Write to memory
		// {{{
		fill = (counts == 0) ? 1 : counts;
		while(mptr < end) {
			STEP(fill, TAPS);
			// fill = (fill&1)?((fill>>1)^TAPS):(fill>>1);
			*mptr++ = fill;
		}
		// }}}

		// Read and compare
		// {{{
		fill = (counts == 0) ? 1 : counts;
		mptr = mem;
		while(mptr < end) {
			STEP(fill, TAPS);
			if (*mptr != (int)fill)
				FAIL;
			mptr++;
		}
		// }}}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// First test done, set the bottom LED
	*_spio = 0x0e04;
	// }}}
#endif
	timestamps[3] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #4, sequential access, read/write 3x at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('3');
	if (1) {
		int	*mptr = mem;
		unsigned fill;

		// Write to memory
		// {{{
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;


			STEP(fill, TAPS);	a = fill;
			STEP(fill, TAPS);	b = fill;
			STEP(fill, TAPS);	c = fill;

			mptr[0] = a;
			mptr[1] = b;
			mptr[2] = c;

			mptr += 3;
		}
		// }}}

		// Read and compare
		// {{{
		mptr = mem;
		fill = counts + 4; if (fill == 0) fill = 1;
		while(mptr+3 < end) {
			register unsigned a, b, c;

			a = mptr[0];
			b = mptr[1];
			c = mptr[2];

			STEP(fill, TAPS);
			if (a != (int)fill)
				FAIL;

			STEP(fill, TAPS);
			if (b != (int)fill)
				FAIL;

			STEP(fill, TAPS);
			if (c != (int)fill)
				FAIL;

			mptr+=3;
		}
		// }}}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Second test done, set the LEDs to reflect that
	*_spio = 0x0e06;
	// }}}
#endif
	timestamps[4] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #5, sequential access, read/write 3x characters at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('4');
	if (1) {
		char	*mcptr;
		unsigned fill;

		// Write to memory
		// {{{
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register char a, b, c;

			STEP(fill, TAPS);	a = fill; // & 0x0ff;
			STEP(fill, TAPS);	b = fill; // & 0x0ff;
			STEP(fill, TAPS);	c = fill; // & 0x0ff;

			mcptr[0] = a;
			mcptr[1] = b;
			mcptr[2] = c;

			mcptr += 3;
		}
		// }}}

		// Read and compare
		// {{{
		mcptr = (char *)mem;
		fill = counts + 19; if (fill == 0) fill = 1;
		while(mcptr+3 < endc) {
			register unsigned a, b, c;

			a = mcptr[0];
			b = mcptr[1];
			c = mcptr[2];

			STEP(fill, TAPS);
			if (((a ^ (int)fill)&0x0ff)!=0)
				FAIL;

			STEP(fill, TAPS);
			if (((b ^ (int)fill)&0x0ff)!=0)
				FAIL;

			STEP(fill, TAPS);
			if (((c ^ (int)fill)&0x0ff)!=0)
				FAIL;

			mcptr+=3;
		}
		// }}}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Third test done
	*_spio = 0x0e08;
	// }}}
#endif
	timestamps[5] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #6, random access, read/write one word at a time
	// {{{
	////////////////////////////////////////////////////////////////////////
	//
	//
	txchr('5');
	{
		int	*mptr = mem;
		unsigned afill, dfill, amsk, initial_afill;

		// Write to memory
		// {{{
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		amsk  = (end-mem) - 1;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill&(~amsk)) == 0)
				mptr[afill&amsk] = dfill;
		} while(afill != initial_afill);
		// }}}

		// Read and compare
		// {{{
		afill = counts;       if (afill == 0) afill = 1;
		dfill = counts + 23;  if (dfill == 0) dfill = 1;
		initial_afill = afill;
		do {
			STEP(afill, TAPS);
			STEP(dfill, TAPS);
			if ((afill & (~amsk)) == 0) {
				if (mptr[afill&amsk] != (int)dfill)
				FAIL;
			}
		} while(afill != initial_afill);
		// }}}
	}
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Fourth test done
	*_spio = 0x0e0a;
	// }}}
#endif
	timestamps[6] = _zip->z_m.ac_ck;
	// }}}
	////////////////////////////////////////////////////////////////////////
	//
	// #7, ZipDMA high speed extended throughput check
	// {{{
#ifdef	_HAVE_ZIPSYS_DMA
	unsigned	ln = (endc + cmem)/2;
	char	*const	midc = &cmem[ln];

	_zip->z_dma.d_rd = cmem;
	_zip->z_dma.d_wr = midc;
	_zip->z_dma.d_len= ln;
	_wbperf->p_control = WBPERF_START | WBPERF_CLEAR;
	_zip->z_dma.d_ctrl = DMACOPY;
	if (_wbperf->p_control == 0)
		txstr("-- NO START\n");
	while(_zip->z_dma.d_ctrl & DMA_BUSY)
		;
	_wbperf->p_control = WBPERF_STOP;
	txstr("6\n0x"); txhex(_wbperf->p_active); txstr(", ");
	txstr("0x"); txhex(_wbperf->p_stb); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_stall); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_stb_ack); txchr("\n");

	txstr("0x"); txhex(_wbperf->p_stall_ack); txstr(", ");
	txstr("0x"); txhex(_wbperf->p_simple_acks); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_wait); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_hold); txchr("\n");

	txstr("0x"); txhex(_wbperf->p_tail); txstr(", ");
	txstr("0x"); txhex(_wbperf->p_bytes); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_write_bytes); txchr(", ");
	txstr("0x"); txhex(_wbperf->p_write_beats); txchr("\n");
#else
	txchr('x');
#endif
#ifdef	_BOARD_HAS_SPIO
	// {{{
	// Fourth test done
	*_spio = 0x0e0c;

	// Toggle bit 0 (0x01) as well--since we just finished another
	// round.  This way the toggling bit will be the indication
	// that the memory controller has been successful.
	*_spio = ((*_spio&0x1)^0x1)|0x0100;
	// }}}
#endif
	timestamps[8] = _zip->z_m.ac_ck;
	txchr('?');
	// }}}
}
// }}}

//
// runtest(void)
// {{{
void	runtest(void) {
	int	counts = 0;
	int	*const mem = (int *)_sdram;
	int	*const end = (int *)(&_sdram[sizeof(_sdram)]);
	unsigned const BLKSIZE = (4u<<20); // 512kB, for 1<<21 < TAPS < 1<<22

#ifdef	_BOARD_HAS_SPIO
	// Clear any/all LED's
	*_spio = 0x0ff00;
#endif

#ifdef	_BOARD_HAS_ZIPSCOPE
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_MANUAL;
#endif

	while(1) {
		int	*run_start, *run_end;

		counts++;
		for(run_start = mem; run_start < end - BLKSIZE;	
					run_start = run_start + BLKSIZE) {
			run_end = run_start + BLKSIZE;
			memchk(run_start, run_end, counts);
		}
	}
}
// }}}

//
// main
// {{{
// Create and start a user task that can then be halted on any error
int	main(void) {
	unsigned zero = 0;
	unsigned	usp[512];

	asm("MOV %0,uR0" : : "r"(zero));
	asm(
	"\tMOV uR0,uR1\n"
	"\tMOV uR0,uR2\n"
	"\tMOV uR0,uR3\n"
	"\tMOV uR0,uR4\n"
	"\tMOV uR0,uR5\n"
	"\tMOV uR0,uR6\n"
	"\tMOV uR0,uR7\n"
	"\tMOV uR0,uR8\n"
	"\tMOV uR0,uR9\n"
	"\tMOV uR0,uR10\n"
	"\tMOV uR0,uR11\n"
	"\tMOV uR0,uR12\n"
	);

	asm("MOV %0,uSP" : : "r"(&usp[511]));
	asm("MOV %0,uPC" : : "r"(runtest));

	zip_rtu();
#ifdef	_BOARD_HAS_ZIPSCOPE
	// If the scope hasn't (yet) triggered, trigger it now
	_zipscope->s_ctrl = SCOPE_DELAY | WBSCOPE_TRIGGER | WBSCOPE_MANUAL;
#endif
#ifdef	_BOARD_HAS_SPIO
	// Activate all LEDs
	*_spio = 0x0ffff;
#endif
	zip_halt();
}
// }}}

