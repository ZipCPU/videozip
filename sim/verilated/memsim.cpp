////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	memsim.cpp
//
// Project:	ZBasic, a generic toplevel impl using the full ZipCPU
//
// Purpose:	This creates a memory like device to act on a WISHBONE bus.
//		It doesn't exercise the bus thoroughly, but does give some
//	exercise to the bus to see whether or not the bus master can control
//	it.
//
//	This particular version differs from the memsim version within the
//	ZipCPU project in that there is a variable delay from request to
//	completion.
//
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
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include "memsim.h"
#include "byteswap.h"

const int	MEMSIM::NWRDWIDTH = 4;

MEMSIM::MEMSIM(const unsigned int nwords, const unsigned int delay) {
	unsigned int	nxt;
	for(nxt=1; nxt < nwords*NWRDWIDTH; nxt<<=1)
		;
	m_len = nxt; m_mask = nxt-1;
	m_mem = new BUSW[m_len];

	m_delay = delay;
	for(m_delay_mask=1; m_delay_mask < delay; m_delay_mask<<=1)
		;
	m_fifo_ack  = new int[m_delay_mask*NWRDWIDTH];
	m_fifo_data = new BUSW[m_delay_mask*NWRDWIDTH];
	for(unsigned i=0; i<m_delay_mask*NWRDWIDTH; i++)
		m_fifo_ack[i] = 0;
	m_delay_mask-=1; m_delay_mask *= NWRDWIDTH;
	m_head = 0; m_tail = (m_head - delay)&m_delay_mask;
}

MEMSIM::~MEMSIM(void) {
	delete[]	m_mem;
}

void	MEMSIM::load(const char *fname) {
	FILE	*fp;
	unsigned int	nr;

	fp = fopen(fname, "r");
	if (!fp) {
		fprintf(stderr, "Could not open/load file \'%s\'\n",
			fname);
		perror("O/S Err:");
		fprintf(stderr, "\tInitializing memory with zero instead.\n");
		nr = 0;
	} else {
		nr = fread(m_mem, sizeof(BUSW), m_len, fp);
		byteswapbuf(nr, m_mem);
		fclose(fp);

		if (nr != m_len) {
			fprintf(stderr, "Only read %d of %d words\n",
				nr, m_len);
			fprintf(stderr, "\tFilling the rest with zero.\n");
		}
	}

	for(; nr<m_len; nr++)
		m_mem[nr] = 0l;
}

void	MEMSIM::load(const unsigned int addr, const char *buf, const size_t len) {
	memcpy(&m_mem[addr], buf, len);
	byteswapbuf(len, &m_mem[addr]);
}

void	MEMSIM::apply(const uchar wb_cyc, const uchar wb_stb, const uchar wb_we,
		const BUSW wb_addr, const uint32_t *wb_data, const short wb_sel,
		unsigned char &o_ack, unsigned char &o_stall, uint32_t *o_data){
	unsigned	sel = 0, addr = wb_addr*NWRDWIDTH;
	const uint32_t	*sp = &wb_data[NWRDWIDTH-1];
	uint32_t	*dp = &o_data[NWRDWIDTH-1];
	uint32_t	wbsel = ((unsigned)wb_sel)&0x0ffff;

	if (!wb_cyc) {
		o_ack = 0;
		o_stall= 0;
		for(unsigned k=0; k<NWRDWIDTH; k++) {
			m_head++;
			m_tail = (m_head - m_delay)&m_delay_mask;
			m_head&=m_delay_mask;
			m_fifo_ack[m_head] = 0;
		}
		return;
	}

	if ((wb_stb)&&(wb_we))
		printf("MEMSIM::WR[%08x]&%5x: ", wb_addr, wbsel);

	m_head += 4;
	m_tail = (m_head - m_delay*4)&m_delay_mask;
	m_head &= m_delay_mask;

	for(unsigned k=0; k<NWRDWIDTH; k++) {
		o_ack = m_fifo_ack[ m_tail + k];
		*dp-- = m_fifo_data[m_tail + k];

		m_fifo_ack[ m_head + k] = 0;
		m_fifo_data[m_head + k] = 0;

		o_stall= 0;
		if ((wb_cyc)&&(wb_stb)) {
			if (wb_we) {
				unsigned dsel  = ((unsigned)wbsel) >> ((NWRDWIDTH-1-k)*4);

				if ((dsel&0x0f)==0x0f) {
					uint32_t memv = *sp--;
					printf("%02x:%02x:%02x:%02x  ",
						(memv>>24)&0x0ff,
						(memv>>16)&0x0ff,
						(memv>> 8)&0x0ff,
						memv&0x0ff);
					m_mem[addr & m_mask] = memv;
				} else {
					uint32_t memv = m_mem[addr & m_mask];

					sel = 0;
					if (dsel&0x8)
						sel |= 0x0ff000000;
					if (dsel&0x4)
						sel |= 0x000ff0000;
					if (dsel&0x2)
						sel |= 0x00000ff00;
					if (dsel&0x1)
						sel |= 0x0000000ff;

					memv &= ~sel;
					memv |= (*sp-- & sel);
					m_mem[addr & m_mask] = memv;

					if (sel&0x0ff000000)
						printf("%02x:", (memv>>24)&0x0ff);
					else
						printf("--:");

					if (sel&0x0ff0000)
						printf("%02x:", (memv>>16)&0x0ff);
					else
						printf("--:");

					if (sel&0x0ff00)
						printf("%02x:", (memv>>8)&0x0ff);
					else
						printf("--:");

					if (sel&0x0ff)
						printf("%02x  ", (memv)&0x0ff);
					else
						printf("--  ");
				}
			}
			m_fifo_ack[m_head + k] = 1;
			m_fifo_data[m_head + k] = m_mem[addr & m_mask];
#define	DEBUG
#ifdef	DEBUG
			printf("MEMBUS %s[%08x] = %08x\n",
				(wb_we)?"W":"R",
				addr&m_mask,
				m_mem[addr&m_mask]);
#endif
		// o_ack  = 1;
		}

#ifdef	DEBUG
		if (o_ack) {
			printf("MEMBUS -- ACK %s 0x%08x - 0x%08x\n",
				(wb_we)?"WRITE":"READ ",
				addr, dp[1]);
		}
#endif
		addr++;
	}

	if ((wb_stb)&&(wb_we))
		printf("\n");
}


