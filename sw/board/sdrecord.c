////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/sdrecord.c
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Records a set of pseudorandom data to an SD card, and then
//		reads it back--proving that data can be written and then read
//	to the SD card.
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
#include "board.h"
// #include "rxfns.h"
#include "txfns.h"
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <locale.h>
#include <zipsys.h>
#include <zipcpu.h>
#include "ffconf.h"
#include "ff.h"

#define	STEP(F,T)	asm volatile("LSR 1,%0\n\tXOR.C %1,%0":"+r"(F):"r"(T))

int main(int argc, char **argv) {
	const	unsigned	DEBUG = 0;
	FATFS	vol;
	FRESULT	r;
	DIR	ds;
	FILINFO	fis;
	const char	FILNAME[] = "testfil.bin";
	const	unsigned	TESTLN = 512*20,
				INVERSION = 0x75ff82ff;
	unsigned	nw, nr, res;
	FIL		fp;
	unsigned	*s, *d, k, seed, fill;
	unsigned	TAPS = 0x0401401;
	unsigned	write_start, write_over, read_start, read_over;

	txstr(
"+----------------------------------+\n"
"|      SDIO Write/Read test        |\n"
"+----------------------------------+\n");

#ifdef	GPIO_SD_RESET_CLR
	*_gpio = GPIO_SD_RESET_CLR;
#endif
	r = f_mount(&vol, "/", 1);
	if (r != FR_OK) {
		printf("Could not mount SD-Card: err %d\n", r);
		printf("TEST FAIL!\n");
		goto failed;
	}

	// Read the main directory
	r = f_opendir(&ds, "/");
	if (r != FR_OK) {
		fprintf(stderr, "F_OPENDIR failed: %d\n", r);
		goto failed;
	}

#ifdef	_BOARD_HAS_SDWBSCOPE
	// Reset the SDWB scope ... if we have it present
	// _sdwbscope->s_ctrl = 0x04000000;
#endif

	s = malloc(TESTLN);
	seed = 7; fill = seed;
	// TAPS => 0x0401401
	//	23 = 0x17 /2 => 0x0040140a
	//	0x00200a05
	//	0x00501103
	//	0x00681c80
	for(k=0; k<TESTLN/4; k++) {
		STEP(fill, TAPS);
		s[k] = fill ^ INVERSION;
	}


	printf("Write test\n"
		"--------------------\n");
	// printf("OPEN:\n");
	// {{{
	res = f_open(&fp, FILNAME, FA_WRITE | FA_CREATE_ALWAYS);
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK ERR\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else
			printf("----> ERR!  FOPEN failed, result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// printf("WRITE:\n");
	// {{{
	nw=0;
	write_start = _zip->z_jiffies;
	res = f_write(&fp, s, TESTLN, &nw);
	write_over  = _zip->z_jiffies;
	if (res != FR_OK) {
		printf("----> ERR!  Write result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	} else if (nw != TESTLN) {
		printf("----> ERR!  Only %d of %d bytes written!\n", nw, TESTLN);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// printf("CLOSE:\n");
	// {{{
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

#ifdef	_BOARD_HAS_SDWBSCOPE
	// _sdwbscope->s_ctrl |= 0xff000000;
#endif

	// Write Time report
	// {{{
	{
		unsigned write_time = write_over - write_start;
		double	write_sec = (write_time * 10e-9);
		double	write_rate = TESTLN / write_sec / 1e3;
		printf("  Write transfer time: %f s (0x%08x clocks)\n", write_sec, write_time);
		printf("  Write transfer rate: %.1f kB/s\n", write_rate);
	}
	// }}}

	if (DEBUG) {
		// {{{
		txstr("Data dump:\n"
			"--------------------\n0x");
		for(k=0; k<TESTLN/4; k++) {
			txhex(s[k]);
			if (k == (TESTLN/4-1))
				txstr("\n");
			else if (127 == (k&0x7f))
				txstr("\n\n0x");
			else if (7 == (k&7))
				txstr("\n0x");
			else
				txstr(" ");
		}
	}
	// }}}

	printf("Read test\n"
		"--------------------\n");
	// Prep memory
	// {{{
	d = malloc(TESTLN);

	// Pre-clear the memory
	for(k=0; k<TESTLN/4; k++)
		d[k] = 0;
	// }}}

	// printf("OPEN:\n");
	// {{{
	res = f_open(&fp, FILNAME, FA_READ);
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK ERR\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else
			printf("----> ERR!  FOPEN failed, result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// printf("READ:\n");
	// {{{
	nr = 0;
	read_start = _zip->z_jiffies;
	res = f_read(&fp, d, TESTLN, &nr);
#ifdef	_BOARD_HAS_SDWBSCOPE
	// _sdwbscope->s_ctrl = 0xff000000;
#else
#error "Scope should be present"
#endif
	read_over = _zip->z_jiffies;
	if (FR_OK != res) {
		if (res == FR_DISK_ERR) {
			printf("----> ERR!  Underlying DISK ERR\n");
		} else if (res == FR_NOT_READY) {
			printf("----> ERR!  Device not ready\n");
		} else if (res == FR_NO_FILE) {
			printf("----> ERR!  File not found\n");
		} else {
			printf("----> ERR!  Read result = %d\n", res);
		}
		printf("TEST FAIL!\n");
		goto failed;
	} else if (nr != TESTLN) {
		printf("----> ERR!  Only %d of %d bytes read!\n", nr, TESTLN);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// printf("CLOSE:\n");
	// {{{
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}
	// }}}

	// Read Time report
	// {{{
	{
		unsigned read_time = read_over - read_start;
		double	read_sec = (read_time * 10e-9);
		double	read_rate = TESTLN / read_sec / 1e3;
		printf("  Read  transfer time: %f s (0x%08x clocks)\n", read_sec, read_time);
		printf("  Read  transfer rate: %.1f kB/s\n", read_rate);
	}
	// }}}


	printf("Verifying data\n"
		"--------------------\n");
	// {{{
	fill = seed;

	int	fail_flag = 0;
	for(k=0; k<TESTLN/4; k++) {
		STEP(fill, TAPS);
		if (d[k] != (fill^INVERSION)) {
			printf("ERR!  PRN[%3d] = %08x doesn't match SD[%3d] = %08x (s[k] = 0x%08x)\n",
				k, fill^INVERSION, k, d[k], s[k]);
			fail_flag = 1;
		}
	} if (fail_flag) {
		if (DEBUG) {
			// {{{
			txstr("Failed Data dump:\n"
				"--------------------\n0x");
			for(k=0; k<TESTLN/4; k++) {
				txhex(d[k]);
				if (k == (TESTLN/4-1))
					txstr("\n");
				else if (127 == (k&0x7f))
					txstr("\n\n0x");
				else if (7 == (k&7))
					txstr("\n0x");
				else
					txstr(" ");
			}
		}
		// }}}
		goto failed;
	}
	// }}}

	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
