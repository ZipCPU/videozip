////////////////////////////////////////////////////////////////////////////////
//
// Filename:	contest.c
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Quick test of the interconnect, make sure everything responds
//		like we are expecting it to.
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
#include "board.h"
#include "txfns.h"
#include "zipcpu.h"

#define	SKIP_BOOTLOADER

asm("\t.section\t.start,\"ax\",@progbits\n"
	"\t.global\t_start\n"
"_start:"	"\t; Here's the global ZipCPU entry point upon reset/reboot\n"
	"\tLDI\t_top_of_stack,SP"	"\t; Set up our supervisor stack ptr\n"
	"\tMOV\t_kernel_is_dead(PC),uPC" "\t; Set user PC pointer to somewhere valid\n"
#ifndef	SKIP_BOOTLOADER
	"\tMOV\t_after_bootloader(PC),R0" " ; JSR to the bootloader routine\n"
	"\tBRA\t_bootloader\n"
"_after_bootloader:\n"
	"\tLDI\t_top_of_stack,SP"	"\t; Set up our supervisor stack ptr\n"
	"\tOR\t0x4000,CC"		"\t; Clear the data cache\n"
#endif
#ifdef	__USE_INIT_FINIT
	"\tJSR\tinit"		"\t; Initialize any constructor code\n"
	//
	"\tLDI\tfini,R1"	"\t; \n"
	"\tJSR\t_atexit"	"\t; Initialize any constructor code\n"
#endif
	//
	"\tCLR\tR1"			"\t; argc = 0\n"
	"\tMOV\t_argv(PC),R2"		"\t; argv = &0\n"
//	"\tLDI\t__env,R3"		"\t; env = NULL\n"
	"\tJSR\tmain"		"\t; Call the user main() function\n"
	//
"_graceful_kernel_exit:"	"\t; Halt on any return from main--gracefully\n"
//	"\tJSR\texit\n"	"\t; Call the _exit as part of exiting\n"
"\t.global\t_exit\n"
"_exit:\n"
	"\tNEXIT\tR1\n"		"\t; If in simulation, call an exit function\n"
"_kernel_is_dead:"		"\t; Halt the CPU\n"
	"\tHALT\n"		"\t; We should *never* continue following a\n"
	"\tBRA\t_kernel_is_dead" "\t; halt, do something useful if so ??\n"
"_argv:\n"
	"\t.WORD\t0,0\n"
	"\t.section\t.text");

void	rwcheckm(const char *str, volatile unsigned *const a, const int mask){
	const unsigned	NONCE = 0x12345678;
	unsigned	original, failed;
	volatile char *const cp = (volatile char *const)a;

	txstr(str);
	original = *a;
	*a = NONCE;
	failed = 0;
	if ((*a & mask) != (NONCE & mask)) {
		failed = 1;
	} if (!failed) {
		*a = ~NONCE;
		if ((*a & mask) != (~NONCE & mask)) {
			failed = 1;
		}
	} if (!failed) {
		*a = mask;
		if ((*a & mask) != mask) {
			failed = 1;
		}
	} if (!failed) {
		*a =  0;
		if ((*a & mask) != 0) {
			failed = 1;
		}
	}

	for(int k=0; (k<4)&&(!failed); k++) {
		unsigned	v, cmsk, wmsk;

		cmsk = (mask >> (8*(3-k))) & 0x0ff;
		if (cmsk == 0)
			continue;
		wmsk = mask & (~(cmsk << (8*(3-k))));

		cp[k] = -1;
		if ((cp[k] & cmsk) != cmsk)
			failed = 1;
		else if ((*a & mask) & wmsk)
			failed = 1;
		cp[k] = 0;
		if (0 != (mask & *a))
			failed = 1;
	}

	if (!failed) {
		*a =  original;
		if (*a != original) {
			failed = 1;
		}
	}

	if (failed)
		txstr(" *** UNEXPECTED ***");
	else
		txstr("(Good)");
	txstr("\r\n");
}

void	rwcheck(const char *str, volatile unsigned *const a) {
	rwcheckm(str, a, -1);
}

void	scopecheck(const char *str, volatile unsigned *const a) {
	const unsigned	NONCE = 0xdbeef, MASK=0x0fffff;
	unsigned	original, mask, ln, failed, v;

	txstr(str);
	original = *a;

	ln = (original >> 20)&0x01f;
	if ((ln < 3)||(ln > 20)) {
		txstr(" *** UNEXPECTED ***\r\n");
		return;
	}

	failed = 0;
	*a = NONCE;
	if ((*a & MASK) != (NONCE&MASK))
		failed = 1;
	if (!failed) {
		*a = (~NONCE)&MASK;
		if (((v = *a) & MASK) != ((~NONCE)&MASK))
			failed = 1;
	} if (!failed) {
		*a = MASK;	// Write all ones
		if (((v = *a) & MASK) != MASK)
			failed = 2;
	} if (!failed) {
		*a =  0;	// Write all zeros
		if (((v = *a) & MASK) != 0)
			failed = 3;
	} if (!failed) {
		*a =  original;	// Return to initial
		if (((v = *a) ^ original)& 0x0fffffff)
			failed = 4;
	}

	if (failed)
		txstr(" *** UNEXPECTED ***");
	else
		txstr("(Good)");

	txstr("\r\n");
}

int main(int argc, char **argv) {
	unsigned pwr;
	char *_sdram = _streamram;

#ifdef	_BOARD_HAS_UARTSCOPE
	_uartscope->s_ctrl = WBSCOPE_DISABLE;
#endif

	txstr(
"+----------------------------------+\n"
"|-   Hardware Connectivity test   -|\n"
"+----------------------------------+\n\n");

	{
		volatile int	a;

		rwcheck("STACK-CHK: ", &a);
	}

	rwcheck("BKRAM-CHK: ", (unsigned *)_bkram);
	rwcheck("SDRAM-CHK: ", (unsigned *)_sdram);

	*_spio = 0x0ff00;
	*_spio = 0x0ff01;
	*_spio = 0x0ff04;
	*_spio = 0x0ff04;
	*_spio = 0x0ff08;
	*_spio = 0x0ff10;
	*_spio = 0x0ff20;
	*_spio = 0x0ff40;
	*_spio = 0x0ff80;
	*_spio = 0x0ffff;

	txstr("VERSION  : "); txhex(*_version);   txstr("\r\n");
	txstr("BUILDTIME: "); txhex(*_buildtime); txstr("\r\n");
	txstr("PWRCOUNT : "); txhex(pwr = *_pwrcount); txstr("\r\n");

	{ // LED check
		unsigned  expected = 1;

		txstr("LED-CHECK: ");
		*_spio = 0x0ffff;
		if (*_spio & 0x0ff != 0x0ff) {
			txstr(" *** Doesn\'t turn on ***");
			expected = 0;
		} else {
			*_spio = 0x0ff00;
			if (*_spio & 0x0ff != 0) {
				expected = 0;
				txstr(" *** Doesn\'t turn off ***");
			}
		} if (expected)
			txstr("Good");

		txstr("\r\n");
	}

	{ // Flash check
		unsigned	v;

		// Don't run this program under flash--it will crash
// #warning "This will crash if running under flash"
		*_flashcfg = 0x1f00;
		v = *_flashcfg;
		*_flashcfg = 0;
		txstr("FLASHCFG : "); txhex(v);
		if ((v & 0x1ff00) != 0x1a00)
			txstr(" *** UNEXPECTED ***");
		txstr("\r\n");
	}

	// txstr("MDIO     : "); txhex(*_buildtime); txstr("\r\n");
	txstr("UART     : "); txhex(_uart->u_setup); txstr(", "); txhex(_uart->u_fifo); txstr("\r\n");
#ifdef	_BOARD_HAS_SDSCOPE
	// scopecheck("SD-SCOPE : ", (unsigned *)&_scope_sdcard->s_ctrl);
#endif
#ifdef	_BOARD_HAS_UARTSCOPE
	txstr("CONSCOPE : ");txhex((unsigned)_uartscope->s_ctrl); txstr("\r\n");
#endif
#ifdef	_BOARD_HAS_ZIPSCOPE
	scopecheck("ZIPSCOPE : ", (unsigned *)&_zipscope->s_ctrl);
#endif
	_zipscope->s_ctrl = 0;
	txstr("GPIO     : "); txhex(*_gpio); txstr("\r\n");
	*_spio = 0x0ff05;
	rwcheck("NETBUF-TX: ", (unsigned *)&_netbtx[0]);
	*_spio = 0x0ff5f;
	// rwcheck("NETBUF-RX: ", (unsigned *)&_netbtx[0]);//RX is read only
	rwcheck("NETP-MAC : ", 1+(unsigned *)&_netp->n_mac);
	if (*_pwrcount == pwr) {
		*_spio = 0x0ffaa;
		txstr("PWRCOUNT : "); txhex(*_pwrcount);
		txstr(" *** DEAD *** \r\n");
	} else {
		txstr("PWRCOUNT : "); txhex(*_pwrcount);
		txstr("\r\n");
	}

	_zipscope->s_ctrl = WBSCOPE_MANUAL;
#ifdef	_BOARD_HAS_UARTSCOPE
	_uartscope->s_ctrl = WBSCOPE_MANUAL;
#endif
	while(_uart->u_tx & 0x0100)
		;
//	asm("NEXIT 0");
	zip_halt();
}
