////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/nexbus.h
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UDP port on an FPGA, to command the WISHBONE on that same
//	FPGA to ... whatever we wish to command it to do.  Both this and the
//	exbus use the same protocol, with only necessary differences.
//
//	This code does not run on an FPGA, is not a test bench, neither is it a
//	simulator.  It is a portion of a command program for commanding an FPGA.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2021-2024, Gisselquist Technology, LLC
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
#ifndef	NEXBUS_H
#define	NEXBUS_H

#include "udpsocket.h"
#include "regdefs.h"
#include "devbus.h"

#define	RDBUFLN	2048

class	NEXBUS : public DEVBUS {
public:
	unsigned long	m_total_nread;
	unsigned	m_gpio;
private:
	// Internal declarations
	// {{{
	UDPSOCKET	*m_dev;
	static	const	unsigned MAXRDLEN, MAXWRLEN, MAXTRIES, PKT_TIMEOUT;

	bool	m_interrupt_flag, m_decode_err, m_txaddr_set, m_rxaddr_set,
		m_bus_err;
	unsigned int	m_txaddr, m_rxaddr;

	int	m_buflen, m_rdfirst, m_rdlast;
	char	*m_buf, *m_rdbuf;

	bool	m_wrloaded, m_syncd;
	int	m_rdaddr, m_wraddr, m_qkaddr;
	BUSW	m_readtbl[512], m_writetbl[512], m_quiktbl[4];

	unsigned	m_rxpos, m_rxlen, m_rxwords;
	BUSW		m_rxdata[1024];

	unsigned	m_frameid, m_rxframeid;
	// }}}

	// Internal function declarations
	// {{{
	void	init(void) {
		m_total_nread = 0;
		m_interrupt_flag = false;
		m_buflen = 8192; m_buf = new char[8192];
		m_txaddr_set = false;
		m_rxaddr_set = false;
		bufalloc(2048);
		m_bus_err = false;
		m_decode_err = false;
		m_wrloaded = false;

		m_rdfirst = m_rdlast = 0;
		m_rdbuf = new char[RDBUFLN];

		m_qkaddr = m_rdaddr = m_wraddr = 0;

		m_dev->bind(UDP_DBGPORT+2);	// Listen to packets from here
		m_dev->connect();
		m_syncd = false;
	}

	char	*begin_packet(const NEXBUS::BUSW a, bool inc=true);
	// char	charenc(const int sixbitval) const;
	// unsigned chardec(const char b) const;
	// void	encode(const int fbits, const BUSW v, char *buf) const;
	// int	decodehex(const char hx) const;
	void	bufalloc(int len);
	BUSW	readword(void); // Reads a word value from the bus
	void	readv(const BUSW a, const int inc, const int len, BUSW *buf);
	void	writev(const BUSW a, const int p, const int len, const BUSW *buf);
	void	readidle(unsigned timeout_ms = 0);
	void	rxgpio(void);
	unsigned	readpkt(unsigned timeout_ms);

	int	lclread(char *buf, int len);
	int	lclreadcode(char *buf, int len);
	char	*encode_address(const BUSW a, bool inc=true);
	char	*readcmd(const int len, char *buf);
	// }}}
public:
	// Constructor / destructors
	// {{{
	NEXBUS(const char *ipaddr) : m_dev(new UDPSOCKET(ipaddr)) { init(); }
	NEXBUS(const char *ipaddr, const unsigned port) : m_dev(new UDPSOCKET(ipaddr, port)) { init(); }
	NEXBUS(UDPSOCKET *comms) : m_dev(comms) { init(); }
	virtual	~NEXBUS(void) {
		m_dev->close();
		if (m_buf) { delete[] m_buf; m_buf = NULL; }
		delete m_rdbuf; m_rdbuf = NULL;
		delete	m_dev;
	}
	// }}}

	void	reset_sync(void);
	void	sync(void);
	// void	reset_device(void);
	void	kill(void) { m_dev->close(); }
	void	close(void) {	m_dev->close(); }
	void	writeio(const BUSW a, const BUSW v);
	BUSW	readio(const BUSW a);
	void	readi( const BUSW a, const int len, BUSW *buf);
	void	readz( const BUSW a, const int len, BUSW *buf);
	void	writei(const BUSW a, const int len, const BUSW *buf);
	void	writez(const BUSW a, const int len, const BUSW *buf);
	bool	poll(void) { return m_interrupt_flag; };
	void	usleep(unsigned msec); // Sleep until interrupt
	void	wait(void); // Sleep until interrupt
	bool	bus_err(void) const { return m_bus_err; };
	void	reset_err(void) { m_bus_err = false; }
	void	clear(void) { m_interrupt_flag = false; }
};

#endif
