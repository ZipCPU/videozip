////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/board/rxfns.c
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019-2024, Gisselquist Technology, LLC
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
//
#include "rxfns.h"
#include "txfns.h"

#define	UARTRX	_uart->u_rx

int	rxchr(void) {
	const	int	echo = 1, cr_into_nl = 1;
	static	int	last_was_cr = 0;
	int	rv;

	rv = UARTRX;
	if (rv & ~0x0ff)
		rv = -1; // Serial port has nothing for us
	else if (cr_into_nl) {
		if (rv == '\r') {
			rv = '\n';
			last_was_cr = 1;
		} else if (rv == '\n') {
			if (last_was_cr) {
				rv = -1;
				last_was_cr = 0;
			}
		} else
			last_was_cr = 0;
	}

	if ((rv != -1)&&(echo))
		txchr(rv);

	return rv;
}

void	rxline(char *str, int ln) {
	int	nrcvd = 0;
	char	*ptr = str;
	int	rxv;

	do {
		rxv = rxchr();
		if (rxv > 0) {
			nrcvd++;
			if (nrcvd >= ln)
				str[ln-1] = 0;
			else {
				nrcvd++;
				*ptr++ = rxv & 0x0ff;
			}
		}
	} while((rxv & 0x0ff) != '\n');
	if (nrcvd >= ln)
		str[ln-1] = 0;
	else
		*ptr = 0;

txstr("Read string: "); txstr(str); txstr("\r\n");
}

int	slen(const char *str) {
	int	ln = 0;
	while(*str++)
		ln++;
	return ln;
}

int	isdig(char v) {
	if (v < 48 || v > 57)
		return 0;
	return 1;
}

int	stoi(const char *str) {
	const char *ptr = str;
	int	dig, nm = 0;

	while(!isdig(*str) && (*str) != 0)
		str++;

	for(dig=0; dig<10; dig++, str++) {
		if (!isdig(*str))
			return nm;
		nm = nm * 10 + (*str& 0x0f);
	}
	return nm;
}


