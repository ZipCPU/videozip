////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/sdreadd.c
// {{{
// Project:	KIMOS, a Mercury KX2 demonstration project
//
// Purpose:	Reads the directory from an SD card, using the FATFS repo,
//		proving it can be read in the first place.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2023-2024, Gisselquist Technology, LLC
// {{{
// This file is part of the KIMOS project.
//
// The KIMOS project is free software and gateware: you can redistribute it
// and/or modify it under the terms of the GNU General Public License as
// published by the Free Software Foundation, either version 3 of the License,
// or (at your option) any later version.
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
#include <zipcpu.h>
#include "ffconf.h"
#include "ff.h"

int main(int argc, char **argv) {
	FATFS	vol;
	FRESULT	r;
	DIR	ds;
	FILINFO	fis;

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

	do {
		r = f_readdir(&ds, &fis);
		if (r != FR_OK) {
			fprintf(stderr, "F_READDIR failed: %d\n");
			goto failed;
		} if (fis.fname[0] == 0) {
			// printf("End of list\n");
			break;
		}

		printf("File: /%s%s\n", fis.fname,
			(fis.fattrib & AM_DIR) ? "/":"");
	} while(1);

	printf("Success\n");
	return 0;

failed:
	fprintf(stderr, "EXIT on failures\n");
}
