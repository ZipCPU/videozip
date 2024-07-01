////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/netsim.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	
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
#include <cassert>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>

#include "udpsocket.h"
#include "netsim.h"
#include "regdefs.h"

#define	RX_IDLE		0
#define	RX_PACKET	1
#define	RX_RUNDOWN	2

#define	TX_IDLE		0
#define	TX_PACKET	1
#define	TX_ERROR	2

#define	NET_BUFSIZE	8192
#define	NET_HEADERSZ	((8+6+6+2)+20+8)

// #define	UDP_DBGPORT
// #define	UDP_DATAPORT

#ifdef	UDP_DBGPORT

NETSIM::NETSIM(void) {
	// {{{
	char	dbgportstr[32], dataportstr[32];
	snprintf(dbgportstr, sizeof(dbgportstr), "127.0.0.1:%d", UDP_DBGPORT);
	snprintf(dataportstr,sizeof(dataportstr),"127.0.0.1:%d", UDP_DATAPORT);
	m_dbgskt  = new UDPSOCKET(dbgportstr);
	m_dataskt = NULL; // m_dataskt = new UDPSOCKET(dataportstr);
	m_dbgskt->bind(UDP_DBGPORT);

	m_rxaddr = 0; m_rxlen = 0; m_rxstate = RX_IDLE;
	m_txaddr = 0; m_txstate = TX_IDLE;

	local_ipu = 0xc0a80002;
	local_ip[0] = 0xc0;
	local_ip[1] = 0xa8;
	local_ip[2] = 0x00;
	local_ip[3] = 0x02;
}
// }}}

unsigned	NETSIM::calc_crc(int pktlen, const unsigned char *buf) {
	// {{{
	const unsigned	TAPS = 0xedb88320;
	unsigned	fill = 0xffffffff;

	for(int p=0; p<pktlen; p++) {
		unsigned char	b = buf[p];

		for(int bit=0; bit<8; bit++) {
			if ((fill ^ b) &1)
				fill = (fill >> 1) ^ TAPS;
			else
				fill >>= 1;

			b >>= 1;
		}
	}

	return fill;
}
// }}}

uint16_t	NETSIM::calc_ipchecksum(int pktlen, const unsigned char *buf) {
	// {{{
	unsigned	checksum = 0;
	unsigned	tmp = 0;

	// printf("CALC-CHECKSUM(LN = %d)\n", pktlen);
	for(int k=0; k<pktlen; k=k+1)
	if ((k&1)==0)
		tmp = buf[k] & 0x0ff;
	else {
		tmp = (tmp << 8) | (buf[k] & 0x0ff);
		checksum = checksum + tmp;
		while (checksum & 0xffff0000)
			checksum = (checksum & 0x0ffff) + 1;
		// printf("BUF[%3d]=%02x, BUF[%3d]=%02x, TMP = %04x, "
		//	"CHECKSUM=%06x\n", k-1, buf[k-1] & 0x0ff, k, buf[k] & 0x0ff,
		//	tmp, checksum);
	}

	if (pktlen & 1) {
		checksum = checksum + (buf[pktlen-1]&0x0ff);
		while (checksum & 0xffff0000)
			checksum = (checksum & 0x0ffff) + 1;
	}

	// printf("-> %04x\n", checksum ^ 0x0ffff);
	return checksum ^ 0x0ffff;
}
// }}}

void	NETSIM::load_header(unsigned char *buf) {
	// {{{
	for(int k=0; k<7; k++)
		buf[k] = 0x55;
	buf[7] = 0xd5;
	for(int k=0; k<6; k++)
		buf[ 8+k] = local_mac[k];
	for(int k=0; k<6; k++)
		buf[14+k] = external_mac[k];

	// IP Ethertype
	buf[20] = 0x08;
	buf[21] = 0x00;
}
// }}}

unsigned	NETSIM::load_arp(unsigned char *buf, unsigned ipaddr) {
	// {{{
	const	unsigned	PL = 22;	// Payload pointer
	unsigned	crc;

	load_header(buf);
	for(int k=0; k<6; k++)
		buf[8+k] = 0xff;

	buf[20] = 0x08;
	buf[21] = 0x06;

	buf[PL+0] = 0x00;	// HTYPE = 1 -> Ethernet
	buf[PL+1] = 0x01;
	buf[PL+2] = 0x08;	// PTYPE = 0x800 -> IPv4
	buf[PL+3] = 0x00;
	buf[PL+4] = 0x06;	// HLEN = 6 for ethernet
	buf[PL+5] = 0x04;	// PLEN = 4 for IPv4
	buf[PL+6] = 0x00;	// Operation = 1
	buf[PL+7] = 0x01;
	for(int k=0; k<6; k++)
		buf[PL+8+k] = external_mac[k];	// Sender's address
	for(int k=0; k<4; k++)
		buf[PL+14+k] = external_ip[k];	// Sender's protocol address
	for(int k=0; k<6; k++)
		buf[PL+18+k] = 0xff;	// Target's hardware address (unknown)
	for(int k=0; k<4; k++)
		buf[PL+24+k] = local_ip[k];	// Target's protocol address
	for(int k=PL+28; k<68; k++)
		buf[k] = 0;

	crc = calc_crc(60, &buf[8]);

	buf[68] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[69] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[70] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[71] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;

	return 72;
}
// }}}

unsigned	NETSIM::load_icmp(unsigned char *buf, unsigned ipaddr) {
	// {{{
	unsigned	crc, checksum;
	const	unsigned	IP = 22;
	const	unsigned	PL = IP+20;	// Payload pointer

	load_header(buf);
	unsigned	ln = 0x54;
	// (8+6+6+2)+(20)+(0x54-20);

	buf[IP+0] = 0x45;
	buf[IP+1] = 0x00;
	buf[IP+2] = 0x00;
	buf[IP+3] = ln; // 20 + 8;	// Packet length: IP Header + Payload

	buf[IP+4] = rand();
	buf[IP+5] = rand();
	buf[IP+6] = 0x00;	// Fragment offset.  We don't support
	buf[IP+7] = 0x00;	// fragmentation, so this must be zero.

	buf[IP+ 8] = 0x40;	// Time to live
	buf[IP+ 9] = 0x01;	// ICMP
	buf[IP+10] = 0x00;	// Checksum
	buf[IP+11] = 0x00;	// Checksum

	buf[IP+12] = external_ip[0];	// Source IP
	buf[IP+13] = external_ip[1];
	buf[IP+14] = external_ip[2];
	buf[IP+15] = external_ip[3];

	buf[IP+16] = local_ip[0];		// Destination IP
	buf[IP+17] = local_ip[1];
	buf[IP+18] = local_ip[2];
	buf[IP+19] = local_ip[3];

	buf[PL+0] = 0x08;	// Echo request
	buf[PL+1] = 0x00;	// Subcode 0
	buf[PL+2] = 0x00;	// Checksum
	buf[PL+3] = 0x00;	// Checksum
	buf[PL+4] = 0x00;	// Subcode 0
	buf[PL+5] = 0x00;	// Subcode 0
	buf[PL+6] = 0x00;	// Subcode 0
	buf[PL+7] = 0x00;	// Subcode 0
	for(unsigned k=PL+8; k<IP+ln; k++)
		buf[k] = rand();

	checksum = calc_ipchecksum(20, &buf[IP]);
	buf[IP+10] = checksum >> 8;
	buf[IP+11] = checksum;

	checksum = calc_ipchecksum(IP+ln-PL, &buf[PL]);
	buf[PL+2] = checksum >> 8;
	buf[PL+3] = checksum;

	crc = calc_crc(IP+ln-8, &buf[8]);

	buf[IP+ln  ] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[IP+ln+1] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[IP+ln+2] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	buf[IP+ln+3] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;

	return IP+ln+4;
}
// }}}

unsigned	NETSIM::load_udp(unsigned ln, unsigned char *buf,
					const struct sockaddr_in *src) {
	// {{{
	unsigned char	*ethptr = buf; // ipptr - (8+6+6+2);
	unsigned char	*ipptr = ethptr + 8+6+6+2; // udpptr - 20;
	unsigned char	*udpptr = ipptr + 20; // buf - 8;
	unsigned	crc, checksum, iplen, pktlen;
	iplen = ln + 8 + 20;

	load_header(ethptr);

	ipptr[0] = 0x45;
	ipptr[1] = 0x00;
	ipptr[2] = (iplen >> 8) & 0x0ff;
	ipptr[3] = (iplen & 0x0ff); // 20 + 8;	// Packet length: IP Header + Payload

	ipptr[4] = rand();
	ipptr[5] = rand();
	ipptr[6] = 0x00;	// Fragment offset.  We don't support
	ipptr[7] = 0x00;	// fragmentation, so this must be zero.

	ipptr[ 8] = 0x40;	// Time to live
	ipptr[ 9] = 0x11;	// UDP
	ipptr[10] = 0x00;	// Checksum
	ipptr[11] = 0x00;	// Checksum

	if (1 && src != NULL) {
		printf("Received from %3d.%3d.%3d.%3d (%08x) : %5d (%04x)\n",
			((src->sin_addr.s_addr      ) & 0x0ff),
			((src->sin_addr.s_addr >>  8) & 0x0ff),
			((src->sin_addr.s_addr >> 16) & 0x0ff),
			((src->sin_addr.s_addr >> 24) & 0x0ff),
			src->sin_addr.s_addr,
			src->sin_port,
			src->sin_port);
	}

	if (src == NULL) {
		ipptr[12] = external_ip[0];	// Source IP
		ipptr[13] = external_ip[1];
		ipptr[14] = external_ip[2];
		ipptr[15] = external_ip[3];
	} else {
		unsigned	addr = ntohl(src->sin_addr.s_addr);
		ipptr[12] = (addr >>24) & 0x0ff; // Source IP
		ipptr[13] = (addr >>16) & 0x0ff;
		ipptr[14] = (addr >> 8) & 0x0ff;
		ipptr[15] = (addr     ) & 0x0ff;
	}

	ipptr[16] = local_ip[0];	// Destination IP
	ipptr[17] = local_ip[1];
	ipptr[18] = local_ip[2];
	ipptr[19] = local_ip[3];

	if (src == NULL) {
		udpptr[0] = (UDP_DBGPORT >> 8)& 0x0ff; // UDP source port
		udpptr[1] = (UDP_DBGPORT     )& 0x0ff;
	} else {
		unsigned port = ntohs(src->sin_port);
		udpptr[0] = (port >> 8)& 0x0ff; // UDP port
		udpptr[1] = (port     )& 0x0ff;
	}
	udpptr[2] = (UDP_DBGPORT >> 8)& 0x0ff; // UDP destination port
	udpptr[3] = (UDP_DBGPORT     )& 0x0ff;

	udpptr[4] = ((ln+8)>>8) & 0x0ff;	// UDP length
	udpptr[5] = ((ln+8)   ) & 0x0ff;
	udpptr[6] = 0;		// Checksum to be filled in
	udpptr[7] = 0;

	checksum = calc_ipchecksum(20, ipptr);
	ipptr[10] = checksum >> 8;
	ipptr[11] = checksum;

	checksum = calc_ipchecksum(ln+8, udpptr);
	udpptr[6] = checksum >> 8;
	udpptr[7] = checksum;

	if (iplen +(6+6+2) < 64) {
		for(unsigned k=0; k<64 - (iplen+6+6+2); k++)
			udpptr[ln+8+k] = 0;
		ln    += 64-(iplen+6+6+2);
		iplen += 64-(iplen+6+6+2);
	}

	crc = calc_crc(iplen + (6+6+2), &ethptr[8]);

	udpptr[ln+ 8] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	udpptr[ln+ 9] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	udpptr[ln+10] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;
	udpptr[ln+11] = (crc & 0x0ff) ^ 0x0ff; crc >>= 8;

	pktlen = iplen + (8+6+6+2) + 4;

	return pktlen;
}
// }}}

void	NETSIM::forward_udp(unsigned ln, unsigned char *buf) {
	// {{{
	unsigned	IP = 8+6+6+2,
			UDP = IP + 20;
	unsigned char *udpptr = buf+UDP;
	unsigned	udpln;
	unsigned short	sport;
	struct sockaddr_in	d;

	UDP = IP + ((buf[IP] & 0x0f) << 2);
	udpln  = (buf[UDP+5] & 0x0ff) | ((buf[UDP+4] & 0x0ff) << 8);
	udpptr = &buf[UDP];
	// printf("INITIAL UDPLN = %d\n", udpln);
	udpln  = udpln-8;	// Minus the UDP header size

	sport = (buf[UDP] << 8) | buf[UDP+1];
	d.sin_family = AF_INET;
	d.sin_port = (buf[UDP+2] << 8) | buf[UDP+3];
	d.sin_addr.s_addr = (buf[IP+16]<<24)
		| (buf[IP+17] << 16) | (buf[IP+18] << 8) | buf[IP+19];

	d.sin_port = htons(d.sin_port);
	d.sin_addr.s_addr = htonl(d.sin_addr.s_addr);

	if (sport == UDP_DBGPORT) {
		/*
		printf("DBGPKT (%d, %d %04x, IP=%d, UDP=%d)\n", ln, udpln,
			udpln, IP, UDP);
		for(unsigned k=0; k<ln; k++) {
			printf("%02x ", buf[k]);
			if (k+1 < ln) {
				if ((k&15)==15)
					printf("\n");
				else if ((k&7)==7)
					printf(" ");
			}
		} printf("\n");
		*/
		m_dbgskt->write(udpln, udpptr+8, &d);
	} else if (sport == UDP_DATAPORT) {
		// printf("DATAPKT\n");
		// m_dataskt->write(udpln, udpptr+8, &d);
	} else
		printf("UNKNOWN SOURCE PORT: %04x\n", sport);
}
// }}}

void	NETSIM::checkudp(unsigned length, const unsigned char *buf) const {
	// {{{
	unsigned pktlen;
	pktlen = ((buf[4]&0x0ff) << 8) | (buf[5] & 0x0ff);
	assert(pktlen == length);

	// We can't check the checksum here, since we don't have the IP header
	// anymore to check it against
}
// }}}

void	NETSIM::checkip(unsigned length, const unsigned char *buf) const {
	// {{{
	unsigned checksum, hdrlen, pktlen;
	const unsigned char *ubuf = (const unsigned char *)buf,
		*iphdr, *payload;

	assert((buf[0] & 0x0f0) == 0x40);
	iphdr   = ubuf;
	hdrlen  = (buf[0] & 0x0f) << 2;
	payload = &iphdr[hdrlen];

	pktlen = (iphdr[2] << 8) | iphdr[3];
	assert(pktlen <= length);
	assert(hdrlen <= pktlen);

	if ((iphdr[11] != 0)||(iphdr[12] != 0)) {
		checksum = NETSIM::calc_ipchecksum(hdrlen, buf);
		// printf("IP CHECKSUM = %04x\n", checksum);
		assert(checksum == 0);
	}

	switch(buf[9]) {
	case 1: // ICMP
		break;
	case 17: // UDP
		checkudp(pktlen-hdrlen, &buf[20]);
		if (payload[6] != 0 || payload[7] != 0) {
			checksum = NETSIM::calc_ipchecksum(pktlen-20, &buf[20]);
			checksum = (~checksum) & 0x0ffff;
			// Now add in the extended header
			checksum = checksum + (payload[4]<<8)+payload[5];
			checksum = checksum + 17;
			// Source IP
			checksum = checksum+ (iphdr[12]<<8) + iphdr[13];
			checksum = checksum+ (iphdr[14]<<8) + iphdr[15];
			// Destination IP
			checksum = checksum+ (iphdr[16]<<8) + iphdr[17];
			checksum = checksum+ (iphdr[18]<<8) + iphdr[19];
			// Reduce the checksum
			checksum = (checksum >> 16) + (checksum & 0x0ffff);
			checksum = (checksum >> 16) + (checksum & 0x0ffff);
			checksum = (~checksum) & 0x0ffff;

			assert(checksum == 0);

			// printf("UDP Checksum matches\n");
		}
		break;
	default:
		break;
	}
}
// }}}

void	NETSIM::checkrx(unsigned length, const unsigned char *buf) const {
	// {{{
	const	unsigned	ETH = 8, IP = 8+6+6+2;
	unsigned	eth_type;
	// printf("TX Packet received\n");
	assert(length >= 64 + ETH);

	// Check for the header
	/*
	printf("PKT:%5d\t", length);
	for(unsigned k=0; k<length; k++) {
		printf("%02x ", buf[k] & 0x0ff);
		if (((k&15) == 15) && k+1 < length)
			printf("\n\t\t");
	}
	printf("\n");
	*/

	// Ethernet synchronization header
	for(int k=0; k<7; k++)
		assert(buf[k] == 0x055);
	assert((buf[7] & 0x0ff) == 0x0d5);

	// Ethertype
	eth_type = ((buf[IP-2] & 0x0ff)<<8) | (buf[IP-1] & 0x0ff);
	// printf("RX Packet, ETHTYPE = %04x\n", eth_type);

	assert(eth_type == 0x0800 || eth_type == 0x0806); // ARP or IP only

	if ((length >= 8+6+6+2+4+20) && eth_type == 0x800) {
		// This is an IP packet
		checkip(length-IP-4, &buf[IP]);
	}
}
// }}}

#endif	// UDP_DBGPORT

unsigned	NETSIM::rxtick(const int resetn) {
	// {{{
#ifdef	UDP_DBGPORT
	unsigned	rv = 0;

	if (resetn == 0) {
		m_rxlen   = 0;
		m_rxaddr  = 0;
		m_rxstate = RX_IDLE;
	} else if (m_rxstate == RX_IDLE) {
		// Poll for any new packets or connections
		if (m_dbgskt) {
			m_rxlen = m_dbgskt->read(NET_BUFSIZE,
				&m_rxdata[NET_HEADERSZ], 0); //, &udp_srcaddr);
		} else
			m_rxlen = 0;

		if (m_rxlen == 0) {
			unsigned	randv;

			randv = rand() & 0x3fff;

			if (randv == 0) {
				m_rxlen = load_arp(m_rxdata,local_ipu);
				// printf(" ARP LEN = %d\n", m_rxlen);
			} else if (randv == 1) {
				m_rxlen = load_icmp(m_rxdata,local_ipu);
				// printf("ICMP LEN = %d\n", m_rxlen);
			}
		} else if (m_rxlen > 0) {
printf("NETSIM::PKT received\n");
			m_rxlen = load_udp(m_rxlen, (unsigned char *)m_rxdata,
				m_dbgskt->source());

			// printf(" UDP LEN = %d\n", m_rxlen);
		}

		if (m_rxlen > 0) {
			m_rxstate = RX_PACKET;
			m_rxaddr  = 0;
		}

		rv = 0x44;
	} else if (m_rxstate == RX_PACKET) {
		rv = 0x100 | (m_rxdata[m_rxaddr++] & 0x0ff);

		if (m_rxaddr >= m_rxlen) {
			m_rxstate = RX_RUNDOWN;
			m_rxlen = rand() & 0x03ff;
		}
	} else {
		rv = 0x44;

		if (m_rxaddr++ >= m_rxlen)
			m_rxstate = RX_IDLE;
	}


	return rv;
#endif
	return 0;
}
// }}}

void	NETSIM::txtick(const int resetn,
				const unsigned ctl, const unsigned txd) {
	// {{{
#ifdef	UDP_DBGPORT
	if (!resetn) {
		// Reset all states
		m_txstate = TX_IDLE;
		m_txaddr  = 0;
	} else {
		// We have a clock, we can act.
		if (m_txstate == TX_PACKET) {
			assert(m_txaddr <= NET_BUFSIZE);
			if (!ctl) {
				const unsigned IP = 8+6+6+2, ETH=8;
				checkrx(m_txaddr, (unsigned char *)m_txdata);
				if (
					(m_txdata[ETH  ] == external_mac[0])
					&&(m_txdata[ETH+1] == external_mac[1])
					&&(m_txdata[ETH+2] == external_mac[2])
					&&(m_txdata[ETH+3] == external_mac[3])
					&&(m_txdata[ETH+4] == external_mac[4])
					&&(m_txdata[ETH+5] == external_mac[5])
					&&(m_txdata[ETH+6+0] == local_mac[0])
					&&(m_txdata[ETH+6+1] == local_mac[1])
					&&(m_txdata[ETH+6+2] == local_mac[2])
					&&(m_txdata[ETH+6+3] == local_mac[3])
					&&(m_txdata[ETH+6+4] == local_mac[4])
					&&(m_txdata[ETH+6+5] == local_mac[5])
					&&(m_txdata[ETH+6+6] == 0x08) // ETHTYPE==IP
					&&(m_txdata[ETH+6+6+1] == 0x00)
					&&(m_txdata[IP] == 0x45) // IP
					&&(m_txdata[IP+9] == 0x11)// UDP Proto
					) {//UDP

					// printf("Forwarding TX packet\n");
					forward_udp(m_txaddr, (unsigned char *)m_txdata);
				}

				m_txstate = TX_IDLE;
				m_txaddr  = 0;
			} else if (m_txaddr == NET_BUFSIZE)
				m_txstate = TX_ERROR;
			else
				m_txdata[m_txaddr++] = txd;
		} else if (m_txstate == TX_ERROR) {
			m_txaddr = 0;
			if (!ctl)
				m_txstate = TX_IDLE;
		} else if (ctl) { // if m_txstate == TX_IDLE
			m_txstate = TX_PACKET;
			m_txaddr  = 0;
			m_txdata[m_txaddr++] = txd;
		}
	}
#endif
}
// }}}


