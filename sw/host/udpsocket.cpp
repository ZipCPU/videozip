////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/udpsocket.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To encapsulate the writing to and reading-from a UDP network
//		port (socket).
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
#include <unistd.h>
#include <strings.h>
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <assert.h>

// #include "port.h"
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdint.h>
// #include "hps.h"
#include <time.h>
#include "udpsocket.h"

#include <poll.h>

		// Where are we connecting to?
const int	DEF_REQUEST_PORT = 6783,
		// Where shall we expect replies?  Only used with bind()
		DEF_REPLY_PORT = DEF_REQUEST_PORT+1;
const char	MY_IP_ADDRESS[] = "192.168.13.1",
		ALT_IP_ADDRESS[] = "127.0.0.1";

UDPSOCKET::UDPSOCKET(const char *fpga_ipaddr, bool verbose) {
	// {{{
	char	*ptr;

	m_connected = false;
	if (NULL == fpga_ipaddr)
		m_skt = -1;
	else {
		char	*ipcopy = strdup(fpga_ipaddr);

		// Create an internet (IP) socket
		// {{{
		m_skt = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
		if (m_skt < 0) {
			fprintf(stderr, "Err: Could not allocate a socket\n");
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		memset((char *)&m_addr, 0, sizeof(m_addr));
		m_addr.sin_family = AF_INET;
		// }}}

		//
		// Get the FPGAs port number
		// {{{
		if (NULL != (ptr = strchr(ipcopy, ':'))) {
			m_addr.sin_port = htons(atoi(ptr+1));
			if (m_addr.sin_port < 1024) {
				fprintf(stderr, "Err: Illegal port!\n");
				exit(EXIT_FAILURE);
			}
		} else {
			// No IP/UDP port is given, assume a default
			m_addr.sin_port = htons(DEF_REQUEST_PORT);
		}
		// }}}

		// Set the IP address
		if (isdigit(ipcopy[0])) { // FPGA IP given by numeric address
			// {{{
			if (NULL != (ptr = strchr(ipcopy, ':')))
				*ptr = '\0';
			if (0 == inet_aton(ipcopy, &m_addr.sin_addr)) {
				fprintf(stderr, "Err: Invalid IP address, %s\n", ipcopy);
				exit(EXIT_FAILURE);
			}
			// }}}
		} else if (isalpha(ipcopy[0])) { // FPGA name given, not address
			// {{{
			struct	hostent	*hp;
			char	*hname = strdup(ipcopy), *ptr;
			if (NULL != (ptr = strchr(hname, ':')))
				*ptr = '\0';
			hp = gethostbyname(hname);
			if (hp == NULL) {
				fprintf(stderr, "Err: Could not get host entity for %s\n", hname);
				perror("O/S Err:");
				exit(EXIT_FAILURE);
			} bcopy(hp->h_addr, &m_addr.sin_addr.s_addr, hp->h_length);

			free(hname);
			// }}}
		} else {
			// {{{
			fprintf(stderr, "Err: Illegal IP address, %s\n", ipcopy);
			exit(EXIT_FAILURE);
			// }}}
		}

		free(ipcopy);
	}
}
// }}}

UDPSOCKET::UDPSOCKET(const char *fpga_ipaddr, unsigned port, bool verbose) {
	// {{{
	m_connected = false;
	if (NULL == fpga_ipaddr)
		m_skt = -1;
	else {
		char	*ipcopy = strdup(fpga_ipaddr);

		// Create an internet (IP) socket
		// {{{
		m_skt = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
		if (m_skt < 0) {
			fprintf(stderr, "Err: Could not allocate a socket\n");
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}

		memset((char *)&m_addr, 0, sizeof(m_addr));
		m_addr.sin_family = AF_INET;
		// }}}

		//
		// Get the FPGAs port number
		// {{{
		m_addr.sin_port = htons(port);
		// }}}

		// Set the IP address
		if (isdigit(ipcopy[0])) { // FPGA IP given by numeric address
			// {{{
			if (0 == inet_aton(ipcopy, &m_addr.sin_addr)) {
				fprintf(stderr, "Err: Invalid IP address, %s\n", ipcopy);
				exit(EXIT_FAILURE);
			}
			// }}}
		} else if (isalpha(ipcopy[0])) { // FPGA name given, not address
			// {{{
			struct	hostent	*hp;
			char	*hname = strdup(ipcopy);

			hp = gethostbyname(hname);
			if (hp == NULL) {
				fprintf(stderr, "Err: Could not get host entity for %s\n", hname);
				perror("O/S Err:");
				exit(EXIT_FAILURE);
			} bcopy(hp->h_addr, &m_addr.sin_addr.s_addr, hp->h_length);

			free(hname);
			// }}}
		} else {
			// {{{
			fprintf(stderr, "Err: Illegal IP address, %s\n", ipcopy);
			exit(EXIT_FAILURE);
			// }}}
		}

		free(ipcopy);
	}
}
// }}}

ssize_t	UDPSOCKET::write(size_t len, const void *buf) const {
	// {{{
	int	flags = MSG_DONTWAIT;	// was zero
	ssize_t	nw;

	if (m_connected) {
		/*
		printf("SEND %d bytes\n\t", (int)len);
		// for(unsigned k=0; k<16 && k < len; k++)
		//	printf("%02x ", ((char *)buf)[k] & 0x0ff);
		for(unsigned k=0; k<len; k++) {
			printf("%02x ", ((char *)buf)[k] & 0x0ff);
			if ((k&15)==15)
				printf("\n\t");
			else if ((k&7)==7)
				printf(" ");
		}
		printf("\n");
		*/
		nw = send(m_skt, buf, len, flags);
	} else {
		nw = sendto(m_skt, buf, len, flags, (struct sockaddr *)&m_addr, 
			sizeof(m_addr));
	}
	return nw;
}
// }}}

ssize_t	UDPSOCKET::write(size_t len, const void *buf, const SOCKADDR *d) const {
	// {{{
	int	flags = MSG_DONTWAIT;	// was zero
	ssize_t	nw;

	// printf("SKT: Sending to %08x : %04x\n", d->sin_addr.s_addr, d->sin_port);
	nw = sendto(m_skt, buf, len, flags,
		(struct sockaddr *)d, sizeof(SOCKADDR));

	if (nw != (ssize_t)len) {
		perror("SKT O/S Err");
	}

	return nw;
}
// }}}

void	UDPSOCKET::connect(void) {
	// {{{
	// m_addr "is the address to which datagrams are sent by default, and
	// the only address from which datagrams are received."
	//
	// Therefore, the client must call connect() although the server need
	// not do so.
	m_connected = true;
	if (::connect(m_skt, (const sockaddr *)&m_addr, sizeof(m_addr)) < 0) {
		perror("Connect O/S Err:");
		exit(EXIT_FAILURE);
	}
}
// }}}

void	UDPSOCKET::bind(unsigned port = DEF_REPLY_PORT) {
	// {{{
	struct	sockaddr_in	my_addr;

	memset(&my_addr, 0, sizeof(struct sockaddr_in));
	my_addr.sin_family = AF_INET;
	my_addr.sin_addr.s_addr = htonl(INADDR_ANY);
	my_addr.sin_port = htons(port);

	if (::bind(m_skt, (struct sockaddr *)&my_addr, sizeof(my_addr)) != 0) {
		perror("Bind O/S Err:");
		exit(EXIT_FAILURE);
	}
}
// }}}

bool	UDPSOCKET::poll(unsigned timeout_ms) {
	// {{{
	struct	pollfd	pollfds;
	int	nr;

	pollfds.fd = m_skt;
	pollfds.events = POLLIN;

	nr = ::poll(&pollfds, 1, timeout_ms);

	if (nr == 0) {
		return false;
	} else if (nr < 0) {
		fprintf(stderr, "Poll error\n");
		perror("O/S Err:");
		return false;
		// exit(EXIT_FAILURE);
	} return true;
}
// }}}

ssize_t	UDPSOCKET::read(size_t len, void *buf, int timeout_ms) {
	// {{{
	int		flags = 0;	// MSG_DONTWAIT is possible here
	ssize_t		nr;
	socklen_t	addrlen = sizeof(m_source);
	// struct	sockaddr_in	si_other;

	if ((timeout_ms >= 0) && !poll(timeout_ms))
		// No packets waiting for us, so ... continue on with life
		return 0;

	// memcpy(&si_other, &m_addr, sizeof(si_other));

	nr = recvfrom(m_skt, buf, len, flags, (sockaddr *)&m_source, &addrlen);
	if (nr < 0) {
		perror("RX O/S Err:");
		exit(-1);
	}
	return nr;
}
// }}}
