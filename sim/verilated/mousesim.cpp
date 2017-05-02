////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	mousesim.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Provides a simulation of a (USB via) PS2 mouse.
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
#include <stdio.h>
#include <stdlib.h>

#include <assert.h>

#include "mousesim.h"

const unsigned MOUSESIM::TICKS_PER_BAUD = 4000;

MOUSESIM::MOUSESIM(void) {
	m_datbuf     = 0;
	m_datbits    = 0;
	m_rxbits     = 0;
	m_datcounter = 0;
	m_waitcount  = 64*TICKS_PER_BAUD;
	// m_last_x = 0;
	// m_last_y = 0;
	m_last_ps2 = 3;
	m_state = MSIM_POWERUP;
	m_idle = false;
	m_xv = 0;
	m_yv = 0;
}

unsigned MOUSESIM::operator()(const unsigned i_ps2) {
	unsigned	ps2, clk, dat;

	// ps2 = (i_ps2)&(m_last_ps2);
	ps2 = i_ps2;
	clk = (ps2&2)?1:0;
	dat = (ps2&1)?1:0;

	if ((m_datcounter > 0)&&(m_datbits > 0)) {
		// printf("MOUSE: TX\n");
		// Currently transmitting
		clk = (m_datcounter < TICKS_PER_BAUD/2)? 0:1;
		dat = m_datbuf&1;
		if (0 == --m_datcounter) {
			m_datbuf >>= 1;
			dat = m_datbuf&1;
			clk = 1;
			if (0 == --m_datbits) {
				// Now done transmitting
				// m_datcounter = 0; 
				dat = 1;
			} else
				m_datcounter = TICKS_PER_BAUD;
		}

		m_idle = false;
	} else if (m_datcounter > 0) {
		// printf("MOUSE: RX\n");
		// Currently receiving
		if (TICKS_PER_BAUD/2 > --m_datcounter) {
			m_datcounter = TICKS_PER_BAUD/2;
			if ((m_last_ps2&2)&&(!clk)) {
				// Negative transition, sample the data
				m_datbuf = (m_datbuf>>1) | (dat<<9);
				m_rxbits++;
				m_datcounter = TICKS_PER_BAUD;

				printf("MOUSE: RXBITS = %d, DATBUF = %03lx\n",
					m_rxbits, m_datbuf);
			}
		} if (11 == m_rxbits) {
			m_datcounter = 0;

			printf("MOUSE: DATA-BYTE-RX: %02lx, parity %d, stop %d\n",
				m_datbuf & 0x0ff, (m_datbuf&0x100)?1:0,
				(m_datbuf&0x0200)?1:0);
				
			printf("DATF = %03lx, TXB = %03lx\n",
				m_datbuf, ((txbyte(m_datbuf&0x0ff)&0x07ff)>>1));
			assert(m_datbuf == ((txbyte(m_datbuf&0x0ff)&0x07ff)>>1));

			m_datbuf&=0x0ff;
			if (0xff == m_datbuf) {
				// Reset request
				m_state = MSIM_RESET_ACK;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = RESET_ACK\n");
			} else if (0x0ea == m_datbuf) {
				m_state = MSIM_STREAM_ACK;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = STREAM_ACK\n");
			} else if (0x0f4 == m_datbuf) {
				m_state = MSIM_DATA_ACK;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = DATA_ACK\n");
			} else {
				printf("MOUSE: Unknown command: 0x%02lx\n", m_datbuf&0x0ff);
				exit(-2);
			}
		}
		m_idle = false;
	} else if (!dat) {
		printf("MOUSE: !DAT\n");
		// Need to start receiving
		m_datbuf = 0;
		m_rxbits = 0;
		m_idle = false;
		m_datcounter = TICKS_PER_BAUD;
	} else if (m_waitcount > 0) {
		// printf("MOUSE: Waitcount = %06x\n", m_waitcount);
		if (0 == --m_waitcount) {
			if (MSIM_POWERUP == m_state) {
				m_datcounter = TICKS_PER_BAUD;
				m_datbuf = txbyte(0x0aa);
				m_datbits = 11;
				m_state = MSIM_BIST;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = BIST, sending a 0x0aa (%lx)\n", m_datbuf);
			} else if (0 < m_datbits) {
				// printf("ZERO-DSTART\n");
				m_datcounter = TICKS_PER_BAUD;
				m_waitcount = TICKS_PER_BAUD*64;
			} else if (MSIM_BIST == m_state) {
				m_datcounter = TICKS_PER_BAUD;
				m_datbuf = txbyte(0x000);
				m_datbits = 11;
				m_state = MSIM_ID;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = ID\n");
			} else if (MSIM_DATA == m_state) {

				unsigned pkt = datapacket();
				m_datbuf = (txbyte((pkt>>16)&0x0ff)&0x07ffl);
				m_datbuf|= (txbyte((pkt>> 8)&0x0ff)&0x07ffl)<<11;
				m_datbuf|= txbyte((pkt    )&0x0ff)<<22;
				m_datcounter = TICKS_PER_BAUD;
				m_datbits = 33;
				m_waitcount = TICKS_PER_BAUD*64;
				// printf("MOUSE: Packet %06x --> %09lx\n", pkt,
					// m_datbuf);
			} else if (MSIM_RESET_ACK == m_state) {
				m_datbuf = txbyte(0xfa);
				m_datbits = 11;
				m_state = MSIM_POWERUP;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = RESET, sending 0xfa\n");
			} else if (MSIM_STREAM_ACK == m_state) {
				m_datbuf = txbyte(0xfa);
				m_datbits = 11;
				m_state = MSIM_STREAM;
				printf("MOUSE: State = STREAM, sending 0xfa\n");
				m_waitcount = TICKS_PER_BAUD*64;
			} else if (MSIM_DATA_ACK == m_state) {
				m_datbuf = txbyte(0xfa);
				m_datbits = 11;
				m_state = MSIM_DATA;
				m_waitcount = TICKS_PER_BAUD*64;
				printf("MOUSE: State = DATA, sending 0xfa\n");
			}
		}
		m_idle = false;
	} else {
		if (!m_idle)
			printf("MOUSE: IDLE\n");
		m_idle = true;
	}

	m_last_ps2 = (clk?2:0)+(dat?1:0);
	m_last_ps2 &= i_ps2;
	return m_last_ps2;
}

unsigned	MOUSESIM::datapacket(void) {
	// An empty data packet: neither button is down, neither
	// has the mouse moved.  Useful for testing the interface alone.
	unsigned	pkt = 0x000000;

	m_xv++;

	m_xv &= 0x01ff;
	m_yv &= 0x01ff;

	pkt = 0x100000;
	if (m_xv & 0x0100)
		pkt |= 0x080000;
	if (m_yv & 0x0100)
		pkt |= 0x040000;
	if (m_xv == 0)
		pkt |= 0x800000;
	pkt |= (m_yv & 0x0ff);
	pkt |= ((m_xv & 0x0ff)<<8);

	return pkt;
}

unsigned long MOUSESIM::txbyte(const unsigned b) {
	// Add a start bit, stop bit, and parity to this byte
	unsigned	p = 1;

	for(int i=0; i<8; i++)
		p ^= (b>>i)&1;

	return ((b&0x0ff)<<1) | (p<<9) | (-1<<10);
}


