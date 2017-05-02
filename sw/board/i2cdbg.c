////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	i2cdbg.c
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
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
#include <stdint.h>
#include <design.h>
#include <cpudefs.h>
#include "board.h"
#include "zipcpu.h"
#include "zipsys.h"

asm("\t.section\t.start\n"
	"\t.global\t_start\n"
	"\t.type\t_start,@function\n"
"_start:\n"
	"\tLDI\t_top_of_stack,SP\n"
	"\tCLR\tCC\n"
	"\tMOV\tbusy_failure(PC),R0\n"
	"\tBRA\tentry\n"
"busy_failure:\n"
	"\tBUSY\n"
	"\t.section\t.text\n");

__attribute__((noinline))
void	wait_while_edout_busy(void) {
	int	this_edcmd;
	while((this_edcmd = (int)_edout->o_cmd) < 0)
		;
}

unsigned	lasti2c[32];


void	txchr(char v);
void	txstr(const char *str);
void	txhex(int num);
void	tx4hex(int num);


__attribute__((noinline))
void	txchr(char v) {
	while(_uart->u_fifo & 0x010000)
		;
	uint8_t c = v;
	_uart->u_tx = (unsigned)c;
}

__attribute__((noinline))
void	txstr(const char *str) {
	const char *ptr = str;
	while(*ptr)
		txchr(*ptr++);
}

__attribute__((noinline))
void	txhex(int num) {
	for(int ds=28; ds>=0; ds-=4) {
		int	ch;
		ch = (num >> ds)&0x0f;
		if (ch >= 10)
			ch = 'A'+ch-10;
		else
			ch += '0';
		txchr(ch);
	}
}

__attribute__((noinline))
void edout_test(int start) {
	unsigned cmd;
	cmd = (0xa10020)|(start<<8);
	txstr("EDOUT.I_CMD : 0x"); txhex(cmd); txstr("\r\n");
	_edout->o_cmd = cmd;
	wait_while_edout_busy();
	txstr("EDOUT.O_CMD : 0x"); txhex(_edout->o_cmd); txstr("\r\n");
	for(int i=0; i<0x08; i++) {
		unsigned addr = (i+start) & 0x07f,
			vl = _edout->o_data[i+start];
		if (lasti2c[addr] != _edout->o_data[addr]) {
			txstr("TXDIF[");txhex(addr);txstr("] = 0x");txhex(vl);txstr("\n");
			lasti2c[addr] = vl;
		}
	}
}

void entry(void) {
	txstr("Starting I2C Debugging program\n");
	*_spio = 0x0ff00;
	_edout->o_spd = 1000; // 100 kHz
	txstr("Waiting while the I2C is busy\n");
	wait_while_edout_busy();

	while(1) {
		edout_test(0x00);
		edout_test(0x08);
		edout_test(0x10);
		edout_test(0x18);
	}
}
