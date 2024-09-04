////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/contest.c
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	A "connection-test".  This is a quick test of the interconnect,
//		just to make sure everything on the bus responds like we are
//	expecting it to.
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
#include "board.h"
#include "regdefs.h"
#include "txfns.h"
#include "zipcpu.h"
// }}}

#define	SKIP_BOOTLOADER

typedef	struct	SDIO_S {
	volatile uint32_t	sd_cmd, sd_data, sd_fifa, sd_fifb, sd_phy,
				sd_unused;
	volatile void		*sd_dma_addr;
	volatile uint32_t	sd_dma_length;
} SDIO;

unsigned	gbl_fail = 0;

void	rwcheckw(const char *str, volatile unsigned *const a, const int mask) {
	// {{{
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

	if (!failed) {
		*a =  original;
		if (*a != original) {
			failed = 1;
		}
	}

	if (failed) {
		txstr(" *** UNEXPECTED ***");
		gbl_fail = 1;
	} else
		txstr("(Good)");
	txstr("\r\n");
}
// }}}

void	rwcheckm(const char *str, volatile unsigned *const a, const int mask) {
	// {{{
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

	if (failed) {
		txstr(" *** UNEXPECTED ***");
		gbl_fail = 1;
	} else
		txstr("(Good)");
	txstr("\r\n");
}
// }}}

void	rwchecka(const char *str, volatile unsigned *const a, const int lsbmsk){
	// {{{
	// Value permits an address, but the number of bits in the address
	// needs to be determined.
	unsigned	o = *a, m;
	*a = -1;
	m = *a;
	if (m == 0 || (m & lsbmsk)) {
		txstr(str);
		txstr(" *** UNEXPECTED ***\r\n");
		txstr("GURU: "); txhex(m); txstr(", "); txhex(lsbmsk); txstr("\r\n");
		gbl_fail = 1;
	} else {
		rwcheckm(str, a, m);
	} *a = o;
}
// }}}

void	rwcheck(const char *str, volatile unsigned *const a) {
	rwcheckm(str, a, -1);
}

void	scopecheck(const char *str, volatile unsigned *const a) {
	// {{{
	const unsigned	NONCE = 0xdbeef, MASK=0x0fffff,
			FIXMSK = 0x0f00000;
	unsigned	original, mask, ln, failed, v;

	txstr(str);
	original = *a;

	ln = (original >> 20)&0x01f;
	if ((ln < 3)||(ln > 20)) {
		gbl_fail = 1;
		txstr(" *** UNEXPECTED ***\r\n");
		return;
	}

	failed = 0;
	*a = NONCE;
	if ((*a & MASK) != (NONCE&MASK) || (((*a ^ original) & FIXMSK) != 0))
		failed = 1;
	if (!failed) {
		*a = (~NONCE)&MASK;
		if (((v = *a) & MASK) != ((~NONCE)&MASK))
			failed = 2;
		if (((v ^ original) & FIXMSK) != 0)
			failed = 3;
	} if (!failed) {
		*a = MASK;	// Write all ones
		if (((v = *a) & MASK) != MASK)
			failed = 4;
		if (((v ^ original) & FIXMSK) != 0)
			failed = 5;
	} if (!failed) {
		*a =  0;	// Write all zeros
		if (((v = *a) & MASK) != 0)
			failed = 6;
		if (((v ^ original) & FIXMSK) != 0)
			failed = 7;
	} if (!failed) {
		*a =  original;	// Return to initial
		if (((v = *a) ^ original)& 0x0fffffff)
			failed = 8;
		if (((v ^ original) & FIXMSK) != 0)
			failed = 9;
	}

	if (failed) {
		txstr(" *** UNEXPECTED ***");
		gbl_fail = 1;
	} else
		txstr("(Good)");

	txstr("\r\n");
}
// }}}

void txhex2(unsigned val) {
	// {{{
	unsigned	v;

	v = (val >> 4) & 0x0f;
	txchr((v > 9) ? (v-10+'A') : (v + '0'));
	v = (val     ) & 0x0f;
	txchr((v > 9) ? (v-10+'A') : (v + '0'));
}
// }}}

int	user_issim(void) {
	// {{{
	asm("CLR R1\n");
	asm("SIM\n");
	asm("LDI 1,R1\n");
	asm("AND 0xffffffdf,CC\n");
	asm("BUSY");
}
// }}}

int	issim(void) {
	// {{{
	volatile int	context[16];
	int	stack[4];	// Overkill, but so what

	for(int k=0; k<16; k++)
		context[k] = 0;
	context[13] = (int)&stack[3];
	context[15] = (int)user_issim;
	zip_restore_context((void *)context);
	zip_rtu();
	zip_save_context((void *)context);
	return	context[1];
}
// }}}

int main(int argc, char **argv) {
	unsigned pwr, rtc;
	// char *_sdram = _streamram;

	txstr(
"+----------------------------------+\n"
"|-   Hardware Connectivity Check  -|\n"
"+----------------------------------+\n\n");

	{
		volatile int	a;

		rwcheck("STACK-CHK   : ", &a);
	}

	if (issim())
		txstr("SIM-CHECK   : Simulation\r\n");
	else
		txstr("SIM-CHECK   : Hardware\r\n");
	if (R_BKRAM != (unsigned)_bkram) {
		txstr("Unexpected BKRAM address\r\n");
		gbl_fail = 1;
	}
	rwcheck("BKRAM-CHK   : ", (unsigned *)_bkram);
	// rwcheck("SDRAM-CHK: ", (unsigned *)_sdram);

	if (R_VERSION != (unsigned)_version) {
		txstr("Unexpected R_VERSION address\r\n");
		gbl_fail = 1;
	} txstr("VERSION     : "); txhex(*_version);   txstr("\r\n");
	if (R_BLDTIME != (unsigned)_buildtime) {
		txstr("Unexpected R_BLDTIME address\r\n");
		gbl_fail = 1;
	} txstr("BUILDTIME   : "); txhex(*_buildtime); txstr("\r\n");
	if (1) {	// Network address reporting
		// {{{
#ifdef	_BOARD_HAS_MEGANET
		unsigned	machi, maclo, ipaddr;
		unsigned long	mac;

		mac   = _net->n_mac;
		machi = (mac >> 32l);
		maclo = mac & 0xffffffffl;
		ipaddr = _net->n_ipaddr;
		txstr("MAC ADDRESS : ");
			txhex2((machi >> 8) & 0x0ff); txstr(":");
			txhex2((machi     ) & 0x0ff); txstr(":");
			txhex2((maclo >>24) & 0x0ff); txstr(":");
			txhex2((maclo >>16) & 0x0ff); txstr(":");
			txhex2((maclo >> 8) & 0x0ff); txstr(":");
			txhex2((maclo     ) & 0x0ff); txstr("\r\n");
		txstr("IP ADDRESS  : ");
			txdecimal((ipaddr >> 24) & 0x0ff); txstr(".");
			txdecimal((ipaddr >> 16) & 0x0ff); txstr(".");
			txdecimal((ipaddr >>  8) & 0x0ff); txstr(".");
			txdecimal((ipaddr     ) & 0x0ff); txstr("\r\n");
#endif
	}
	// }}}

	// Pre-checks: PWRCOUNT && RTCCOUNT
	// {{{
#ifdef	PWRCOUNT_ACCESS
	if (R_PWRCOUNT != (unsigned)_pwrcount) {
		txstr("Unexpected R_PWRCOUNT address\r\n");
		gbl_fail = 1;
	} pwr = *_pwrcount;
#endif	// PWRCOUNT_ACCESS
#ifdef	_BOARD_HAS_RTCCOUNT
	if (R_RTCCOUNT != (unsigned)_rtccount) {
		txstr("Unexpected R_RTCCOUNT address\r\n");
		gbl_fail = 1;
	} rtc = *_rtccount;
#endif
	// }}}

	if (1) { // Flash check
		// {{{
#ifdef	_BOARD_HAS_FLASHCFG
		unsigned	*mainp = (unsigned *)main;
		if (R_FLASHCFG != (unsigned)_flashcfg) {
			txstr("Unexpected R_FLASHCFG address\r\n");
			gbl_fail = 1;
		} else if ((mainp < (unsigned *)&_flash[0]) || (mainp >= (unsigned *)&_flash[0x01000000])) {
		// Flash check
			unsigned	v;

			// Don't run this program under flash--it will crash
			// Turn on and then off configuration mode, read the
			// result--make certain you can read the configuration
			// register bits.  This does not actually talk to the
			// flash.
// #warning "This will crash if running under flash"
			*_flashcfg = 0x1f00;
			v = *_flashcfg;
			*_flashcfg = 0;
			txstr("FLASHCFG    : ");
			if ((v & 0x1ff00) != 0x1a00) {	// 0x1a?? comes from controller
				gbl_fail = 1;
				txhex(v);
				txstr(" -- *** UNEXPECTED ***\r\n");
			} else
				txstr("(Good)\r\n");
		}
#endif
	}
	// }}}

	// PWRCOUNT
	// {{{
#ifdef	PWRCOUNT_ACCESS
	if (*_pwrcount == pwr) {
		txstr("PWRCOUNT    : "); txhex(*_pwrcount);
		txstr(" *** DEAD *** \r\n");
		gbl_fail = 1;
	} else {
		txstr("PWRCOUNT    : "); txhex(*_pwrcount);
		txstr("\r\n");
	}
#endif
#ifdef	_BOARD_HAS_RTCCOUNT
	txstr("RTCCOUNT    : "); txhex(*_rtccount);
	if (*_rtccount == rtc) {
		txstr(" *** DEAD *** \r\n");
		gbl_fail = 1;
	} else {
		txstr("\r\n");
	}
#endif
	// }}}

	if (1) { // I2C
		// {{{
#ifdef	_BOARD_HAS_I2CCPU
		unsigned	v;

		if (R_I2CCPU != (unsigned)_i2c) {
			gbl_fail = 1;
			txstr("Unexpected R_I2CCPU address\r\n");
		} else if ((v=_i2c->ic_control) & 0x00080000) {
			rwcheckw("I2CCPU.CLK  : ",
				(unsigned *)&_i2c->ic_clkcount, 0x0fff);
		} else {
			txstr("I2CCPU      : (Busy -- check skipped, ");
			txhex(v);
			txstr(")\r\n");
		}
#endif
	}
	// }}}

	if (1) { // MDIO check
		// {{{
#ifdef	_BOARD_HAS_NETMDIO
		unsigned	v;
		//if (R_MDIO_PHYIDR1 != (unsigned)&_mdio->e_v[1][MDIO_PHYIDR1])
		//	gbl_fail = 1;
		//if (R_MDIO_PHYIDR2 != (unsigned)&_mdio->e_v[1][MDIO_PHYIDR2])
		//	gbl_fail = 1;
		txstr("MDIO.PHYIDR1: ");
		if ((v = _mdio->e_v[1][MDIO_PHYIDR1]) != 0x01c) {
			txstr("FAIL -- ID returns "); txhex(v);
			gbl_fail = 1;
		} else
			txstr("(Good)");
		txstr("\r\n");
		txstr("MDIO.PHYIDR2: ");
		if ((v = _mdio->e_v[1][MDIO_PHYIDR2]) != 0xc915) {
			txstr("FAIL -- ID returns "); txhex(v);
			gbl_fail = 1;
		} else
			txstr("(Good)");
		txstr("\r\n");
#endif
	}
	// }}}

	// Check for ... GENCLKFB

	// Check for ... SPIO
	// {{{
#ifdef	SPIO_ACCESS
	if (R_SPIO != (unsigned)_spio) {
		txstr("Unexpected R_SPIO address\r\n");
		gbl_fail = 1;
	} else {
		unsigned	orig = *_spio, msk, m, failed = 0;

		if (!failed)
			txstr("SPIO LED CHK: ");
		// Count how many LEDs we have
		*_spio = 0x0ffff;	// Turn all LEDs on (if possible)
		msk = *_spio & 0x0ff;
		*_spio = 0xff00;
		if ((*_spio & 0x0ff) != 0) {
			txstr("SPIO FAIL\r\n");
			failed = 1;
			gbl_fail = 1;
		}
		// Toggle each individual LED
		else if (msk != 0) for(m=1; (m&msk) && !failed; m <<= 1) {
			*_spio = m | (m << 8);
			if (0 == (*_spio & m)) {
				txstr("SPIO FAIL\r\n");
				failed = m << 1;
				gbl_fail = 1;
			}
		} if (orig & 0x1000000)
			*_spio = 0x1000000;
		else
			*_spio = orig | 0x0ff00;

		if (!failed)
			txstr("(Good)\n");
	}
#endif
	// }}}

	// Check for ... SDIO
	// {{{
#ifdef	_BOARD_HAS_SDIO
	if (R_SDIO_CTRL != (unsigned)_sdio) {
		txstr("Unexpected R_SDIO address\r\n");
		gbl_fail = 1;
	} else {
		unsigned	v;

		v = _sdio->sd_cmd;
		// The SD card will only pass if it's not in reset, and it'll
		// only not be in reset if the card removed signal isn't set.
		if (v & 0x080000) {
			txstr("SDIO.CMD    : No card present\r\n");
		} else {
			if (v & 0x040000)
				_sdio->sd_cmd = 0x040000;
			v = _sdio->sd_cmd;
			rwchecka("SDIO.DMAADDR: ", (unsigned *)&_sdio->sd_dma_addr, 0);

			if (0 == (v & 0x80000)) {
				// A card is present, so we can check the ARG and
				// DMA length
				rwcheck( "SDIO.ARG    : ", (unsigned *)&_sdio->sd_data);
				rwcheck( "SDIO.DMALN  : ", (unsigned *)&_sdio->sd_dma_length);
			}
		}
	}
#else
	txstr("SDIO        : (Not installed)\r\n");
#endif
	// }}}

	// Check for ROTARY encoder
#ifdef	_BOARD_HAS_ROTARY
	rwcheckm("ROTARY ENC  : ", _rotary, 0xffffffff);
#endif
	if (1) { // Check for OLEDBW
		// {{{
#ifdef	_BOARD_HAS_OLEDBW
		unsigned	v;

		if (R_OLED != (unsigned)_oled) {
			gbl_fail = 1;
			txstr("Unexpected R_OLED address\r\n");
		} else if (0 == ((v=_oled->o_cmd) & 1)) {
			rwcheckw("OLED.CLK    : ",
				(unsigned *)&_oled->o_clk, 0x0ffe);
		} else {
			txstr("OLED        : (Busy -- check skipped, ");
			txhex(v);
			txstr(")\r\n");
		}
#endif
	}
	// }}}

	// Check for RTC	--- but what test to use?
	txstr("REALTIMECLK : "); txhex(_rtc->r_clock); txstr("\n");
	// Check for RTCDATE	--- but what test to use?
	txstr("REALTIMEDATE: "); txhex(*_rtcdate); txstr("\n");

	if (!issim()) { // Check for ICAPETWO
		// {{{
#ifdef	_BOARD_HAS_ICAPETWO
		if (R_CFG_WBSTAR != (unsigned)&_icape[CFG_WBSTAR]) {
			gbl_fail = 1;
			txstr("Unexpected ICAPE2 address\r\n");
		} else
			rwcheckw("ICAPE.WBSTAR: ",&_icape[CFG_WBSTAR],0x0ffffff);
#else
		txstr("ICAPE2 CHECK: (SKIPPED! -- Not installed)\n");
#endif
	}
	// }}}

	if (1) { // Check for VIDPIPE
		// {{{
#ifdef	_BOARD_HAS_VIDPIPE
		if (R_VIDPIPE != (unsigned)&_hdmi->v_control) {
			gbl_fail = 1;
			txstr("Unexpected VIDPIPE address\r\n");
		} else {
			unsigned	msk;
			volatile unsigned *_sz;

			_sz = (unsigned *)&_hdmi->v_in.m_height;
			*_sz = -1;
			msk = *_sz;
			rwcheckw("VIDPIPE.SIZE: ", (unsigned *)_sz,msk);
		}
#endif
	}
	// }}}

	// Scope checks
	// {{{
#ifdef	_BOARD_HAS_FLASHSCOPE
	scopecheck("FLASHSCOPE  : ", (unsigned *)&_flashscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_VIDSCOPE
	scopecheck("VIDSCOPE    : ", (unsigned *)&_zipscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_SDIOSCOPE
	scopecheck("SDIOSCOPE   : ", (unsigned *)&_sdioscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_SDWBSCOPE
	scopecheck("SDWBSCOPE   : ", (unsigned *)&_sdwbscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_EDIDSLVSCOPE
	scopecheck("EDIDSLVSCOPE: ", (unsigned *)&_edidslvscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_EDIDSCOPE
	scopecheck("EDIDSCOPE   : ", (unsigned *)&_edidscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_I2CSCOPE
	scopecheck("I2CSCOPE    : ", (unsigned *)&_i2cscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_I2SSCOPE
	scopecheck("I2SSCOPE    : ", (unsigned *)&_i2sscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_MDIOSCOPE
	scopecheck("MDIOSCOPE   : ", (unsigned *)&_mdioscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_SPISCOPE
	scopecheck("SPISCOPE    : ", (unsigned *)&_spiscope->s_ctrl);
#endif
#ifdef	_BOARD_HAS_ZIPSCOPE
	scopecheck("ZIPSCOPE    : ", (unsigned *)&_zipscope->s_ctrl);
	_zipscope->s_ctrl = 0;
#endif
	// }}}

	txstr("GPIO        : "); txhex(*_gpio); txstr("\r\n");

	// Return to pwr count and RTC counts
	// {{{
#ifdef	PWRCOUNT_ACCESS
	if (*_pwrcount == pwr) {
		*_spio = 0x0ffaa;
		txstr("PWRCOUNT    : "); txhex(*_pwrcount);
		txstr(" *** DEAD *** \r\n");
	} else {
		txstr("PWRCOUNT    : "); txhex(*_pwrcount);
		txstr("\r\n");
	}
#endif
#ifdef	_BOARD_HAS_RTCCOUNT
	txstr("RTCCOUNT    : "); txhex(*_rtccount);
	if (*_rtccount == rtc) {
		txstr(" *** DEAD *** \r\n");
		gbl_fail = 1;
	} else {
		txstr("\r\n");
	}
#endif
	// }}}

	_zipscope->s_ctrl = WBSCOPE_MANUAL;
#ifdef	_BOARD_HAS_UARTSCOPE
	_uartscope->s_ctrl = WBSCOPE_MANUAL;
#endif

	txstr("--------------------------------\r\n");
	if (gbl_fail)
		txstr("TEST FAIL\r\n");
	else
		txstr("TEST SUCCESS\r\n");
	txstr("\r\n");
	while(_uart->u_tx & 0x0100)
		;
	*_gpio = GPIO_HALT_SET;
	zip_halt();
}
