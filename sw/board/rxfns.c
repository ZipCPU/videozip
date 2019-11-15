////////////////////////////////////////////////////////////////////////////////
//
// Filename:	rxfns.c
//
// Project:	N68335-19-C-0379
//
// Purpose:
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2019, Gisselquist Technology, LLC
//
// The algorithms described in this file are proprietary to Gisselquist
// Technology, LLC.  They may not be redistributed without the express
// permission of an authorized representative of Gisselquist Technology.
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


