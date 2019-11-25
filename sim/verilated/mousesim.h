////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	mousesim.h
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
// Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
#ifndef	MOUSESIM_H
#define	MOUSESIM_H

class	MOUSESIM {
	typedef	enum {
		MSIM_POWERUP,
		MSIM_BIST,
		MSIM_ID,
		MSIM_STREAM,
		MSIM_DATA,
		MSIM_RESET_ACK,
		MSIM_STREAM_ACK,
		MSIM_DATA_ACK
	} MSIM_STATES;

	MSIM_STATES	m_state;
	unsigned long	m_datbuf;
	unsigned	m_datbits, m_datcounter, m_waitcount, m_last_ps2,
			m_rxbits;
	static const unsigned	TICKS_PER_BAUD;
	bool		m_idle;
	int		m_xv, m_yv;

public:
	MOUSESIM(void);
	unsigned operator()(const unsigned i_ps2);
	unsigned	datapacket(void);
	unsigned long	txbyte(const unsigned b);
};

#endif
