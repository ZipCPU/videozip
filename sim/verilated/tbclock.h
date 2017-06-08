////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	tbclock.h
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
#ifndef	TBCLOCK_H
#define	TBCLOCK_H

class	TBCLOCK	{
	unsigned long	m_increment, m_now, m_last_edge;

public:
	TBCLOCK(unsigned long increment) {
		m_increment = (increment>>1)&-2l;
		assert(m_increment > 0);

		// Start with the clock low, waiting on a positive edge
		m_now = m_increment+1;
		m_last_edge = 0;
	}

	unsigned long	time_to_tick(void) {
		if (m_last_edge + m_increment < m_now)
			return (m_last_edge + 2*m_increment - m_now);
		else
			return (m_last_edge +   m_increment - m_now);
	}

	int	advance(unsigned long itime) {
		m_now += itime;
		if (m_now >= m_last_edge + 2*m_increment) {
			m_last_edge += 2*m_increment;
			return 1;
		} else if (m_now >= m_last_edge + m_increment)
			return 0;
		else
			return 1;
	}

	bool	rising_edge(void) {
		if (m_now == m_last_edge)
			return true;
		return false;
	}

	bool	falling_edge(void) {
		if (m_now == m_last_edge + m_increment)
			return true;
		return false;
	}

};
#endif
