////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/netsim.h
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Simulate an (R)GMII interface.
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
#ifndef	NETSIM_H
#define	NETSIM_H

#include <cassert>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>

#include "udpsocket.h"

#define	NET_BUFSIZE	8192

// #define	UDP_DBGPORT
// #define	UDP_DATAPORT


class	NETSIM {
	UDPSOCKET		*m_dbgskt, *m_dataskt;
	struct sockaddr_in	udp_srcaddr;
public:
	void	checkudp(unsigned length, const unsigned char *buf) const;
	void	checkip(unsigned length, const unsigned char *buf) const;
	void	checkrx(unsigned length, const unsigned char *buf) const;
	void	forward_udp(unsigned len, unsigned char *buf);

	static	unsigned	calc_crc(int pktlen, const unsigned char *buf);
	static	uint16_t	calc_ipchecksum(int pktlen, const unsigned char *buf);
	void		load_header(unsigned char *buf);
	unsigned	load_arp(unsigned char *buf, unsigned ipaddr);
	unsigned	load_icmp(unsigned char *buf, unsigned ipaddr);
	unsigned	load_udp(unsigned len, unsigned char *buf,
					const struct sockaddr_in *src = NULL);
public:
	unsigned char	external_mac[6], local_mac[6];
	unsigned char	external_ip[4], local_ip[4];
	unsigned	local_ipu;

	unsigned	m_rxaddr, m_rxlen, m_rxstate;
	unsigned char	m_rxdata[NET_BUFSIZE];

	unsigned	m_txstate, m_txaddr;
	unsigned char	m_txdata[NET_BUFSIZE];

	NETSIM(void);
	unsigned	rxtick(const int resetn);
	void		txtick(const int resetn,
				const unsigned ctl, const unsigned txd);
	unsigned	operator()(const int resetn,
				const unsigned txctl, const unsigned txd) {
		txtick(resetn, txctl, txd);
		return rxtick(resetn);
	}
};

#endif	// NETSIM_H
