////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/devbus.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	The purpose of this file is to document an interface which
//		any device with a bus, whether it be implemented over a UART,
//	an ethernet, or a PCI express bus, must implement.  This describes
//	only an interface, and not how that interface is to be accomplished.
//
//	The neat part of this interface is that, if programs are designed to
//	work with it, than the implementation details may be changed later
//	and any program that once worked with the interface should be able
//	to continue to do so.  (i.e., switch from a UART controlled bus to a
//	PCI express controlled bus, with minimal change to the software of
//	interest.)
//
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
#include <string.h>
#include <unistd.h>
#include <assert.h>

#include "regdefs.h"
#include "port.h"
#include "devbus.h"
#ifdef	UDP_DBGPORT
#include "nexbus.h"
#endif
#include "exbus.h"

#ifndef	UARTDBGPORT
#define	UARTDBGPORT	5927
#endif

const	char	*gbl_devname = "VIDEODEV";

DEVBUS	*connect_devbus(const char *ustr) {
	const char *str, *start = NULL;
	bool	tty_flag = false;
	DEVBUS	*devbus = NULL;

	str = ustr;
	if (NULL == ustr || '\0' == ustr[0])
		str = getenv(gbl_devname);
	if (NULL == str) {
		fprintf(stderr, "ERR: No device defined\n");
		exit(EXIT_FAILURE);
	}

	if (0==strncasecmp(str, "UART://", 7)) {
		tty_flag = true; start = &str[7];
	} else if (0==strncasecmp(str, "EXBUS://", 9)) {
		tty_flag = true; start = &str[9];
	} else if (0==strncasecmp(str, "TTYBUS://", 9)) {
		tty_flag = true; start = &str[9];
	} else if (0==strncasecmp(str, "SIM://", 6)) {
		tty_flag = true; start = &str[6];
	} else if (0==strncasecmp(str, "NET://", 6)) {
		tty_flag = false; start = &str[6];
	} else if (0==strncasecmp(str, "UDP://", 6)) {
		tty_flag = false; start = &str[6];
	} else if (0==strncasecmp(str, "NETBUS://", 9)) {
		tty_flag = false; start = &str[9];
	} else {
		tty_flag = true; start = str;
	}

	char		*host, *ptr;
	unsigned	udp_port;

	host = strdup(start);
	ptr = strchr(host, ':');

	if (NULL == ptr) {
#ifdef	UDP_DBGPORT
		udp_port = (tty_flag) ? UARTDBGPORT : UDP_DBGPORT;
#else
		udp_port = UARTDBGPORT;
#endif
	} else {
		udp_port = atoi(ptr + 1);
		*ptr = '\0';
	}

	if (tty_flag) {
		devbus = new EXBUS(new NETCOMMS(host, udp_port));
	} else {
#ifdef	UDP_DBGPORT
		devbus = new NEXBUS(host, udp_port);
#else
		fprintf(stderr, "ERR: No network bus defined\n");
		exit(EXIT_FAILURE);
#endif
	}

	free(host);
	return devbus;
}

