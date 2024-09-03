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
	FATFS	vol;
	FRESULT	r;
	DIR	ds;
	FILINFO	fis;
	const char	FILNAME[] = "testfil.bin";
	const	unsigned	TESTLN = 512*20;
	unsigned	nw, nr, res;
	FIL		fp;
	unsigned	*s, *d, k, seed, fill;
	unsigned	TAPS = 0x0401401;
	unsigned	write_start, write_over, read_start, read_over;

#ifdef	GPIO_SD_RESET_CLR
	*_gpio = GPIO_SD_RESET_CLR;
#endif
	r = f_mount(&vol, "/", 1);
	if (r != FR_OK)
		printf("Could not mount SD-Card: err %d\n", r);

	// Read the main directory
	r = f_opendir(&ds, "/");
	if (r != FR_OK) {
		fprintf(stderr, "F_OPENDIR failed: %d\n", r);
		goto failed;
	}

	s = malloc(TESTLN);
	seed = 1; fill = seed;
	for(k=0; k<TESTLN/4; k++) {
		STEP(fill, TAPS);
		s[k] = fill;
	}


	printf("Write test\n"
		"--------------------\n");
	// printf("OPEN:\n");
	f_open(&fp, FILNAME, FA_WRITE | FA_CREATE_ALWAYS);
	// printf("WRITE:\n");
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

	// printf("CLOSE:\n");
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}

	{
		unsigned write_time = write_over - write_start;
		double	write_sec = (write_time * 10e-9);
		double	write_rate = TESTLN / write_sec / 1e3;
		printf("  Write transfer time: %f s (0x%08x clocks)\n", write_sec, write_time);
		printf("  Write transfer rate: %.1f kB/s\n", write_rate);
	}

	printf("Read test\n"
		"--------------------\n");
	d = malloc(TESTLN);
	// printf("OPEN:\n");
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
	// printf("READ:\n");
	read_start = _zip->z_jiffies;
	res = f_read(&fp, d, TESTLN, &nr);
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

	// printf("CLOSE:\n");
	res = f_close(&fp);
	if (res != FR_OK) {
		printf("----> ERR!  Close result = %d\n", res);
		printf("TEST FAIL!\n");
		goto failed;
	}

	{
		unsigned read_time = read_over - read_start;
		double	read_sec = (read_time * 10e-9);
		double	read_rate = TESTLN / read_sec / 1e3;
		printf("  Read  transfer time: %f s (0x%08x clocks)\n", read_sec, read_time);
		printf("  Read  transfer rate: %.1f kB/s\n", read_rate);
	}


	printf("Verifying data\n"
		"--------------------\n");
	seed = 1; fill = seed;
	for(k=0; k<TESTLN/4; k++) {
		STEP(fill, TAPS);
		if (d[k] != fill) {
			printf("ERR!  PRN[%d] = %08x doesn't match SD[%d] = %08x\n", k, fill, k, d[k]);
			goto failed;
		}
	}


	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
