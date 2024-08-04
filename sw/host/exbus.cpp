////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sw/host/exbus.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This is the C++ program on the command side that will interact
//		with a UART on an FPGA, to command the WISHBONE on that same
//	FPGA to ... whatever we wish to command it to do.
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
//
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <termios.h>
#include <netinet/in.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <arpa/inet.h>
#include <assert.h>
#include <strings.h>
#include <poll.h>
#include <ctype.h>

#include "exbus.h"
// }}}

const	unsigned EXBUS::MAXRDLEN = 32; // 1024;
const	unsigned EXBUS::MAXWRLEN = 32;

// Debug DBGPRINTF infrastructure
// {{{
// #define	DBGPRINTF	printf
// #define	DBGPRINTF	filedump
#ifndef	DBGPRINTF
#define	DBGPRINTF	null
#else
#define	EXDEBUG
#warning "EXBUS DEBUG IS TURNED ON"
#endif

void	null(...) {}

#include <stdarg.h> // replaces the (defunct) varargs.h include file
void	filedump(const char *fmt, ...) {
// {{{
	static	FILE *dbgfp = NULL;
	va_list	args;

	if (!dbgfp) {
		dbgfp = fopen("debug.txt", "w");
		// fprintf(dbgfp, "\n\n\n-----------------------------\n");
		// fprintf(dbgfp, "     NEW TRANSACTION \n");
		// fprintf(dbgfp, "-----------------------------\n");
	}
	va_start(args, fmt);
	vfprintf(dbgfp, fmt, args);
	va_end(args);
	fflush(dbgfp);

	// If you want the debug output to go to stderr as well, you can
	// uncomment the next couple of lines
	// va_start(args, fmt);
	// vfprintf(stderr, fmt, args);
	// va_end(args);
}
// }}}
// }}}

//
// bufalloc
// {{{
// Allocate a buffer of at least length (len).  This is similar to realloc().
//
void	EXBUS::bufalloc(int len) {
	if ((m_buf)&&(m_buflen >= len))
		return;
	if (m_buf)
		delete[] m_buf;
	m_buflen = (len&(-0x3f))+0x40;
	m_buf = new char[m_buflen];
}
// }}}

//
// lclreadcode
// {{{
int	EXBUS::lclreadcode(char *buf, int len) {
	int	nr, ret;

	nr = m_dev->read(buf, len);
#ifdef	EXDEBUG
	if (nr > 0) {
		DBGPRINTF("EXDEV.READ %d: ", nr);
		for(int k=0; k<nr-1; k++)
			DBGPRINTF("%02x:", buf[k] & 0x0ff);
		DBGPRINTF("%02x\n", buf[nr-1] & 0x0ff);
	}
#endif
	m_total_nread += nr;
	ret = nr;
	// Normally, we'd skip any invalid codewords here.  The EXBUS, however,
	// doesn't use invalid codewords--so we therefore return everything.
	return ret;
}
// }}}

//
// writeio
// {{{
// Write a single value to the debugging interface
//
void	EXBUS::writeio(const BUSW a, const BUSW v) {

	writev(a, 0, 1, &v);
	m_txaddr = a; m_txaddr_set = true;
}
// }}}

//
// writev
// {{{
// This internal write function.  This writes a buffer of information to our
// interface, and the place to study how a write works.
//
// Parameters:
//	a	is the address to write to
//	p	=1 to increment address, 0 otherwise
//	len	The number of values to write to the bus
//	buf	A memory pointer to the information to write
//
// Notice that this routine can only write complete 32-bit words.  It doesn't
// really have any 8-bit byte support, although you might be able to create such
// by readio()'ing a word, modifying it, and then calling writeio() to write the
// modified word back.
//
void	EXBUS::writev(const BUSW a, const int p, const int len, const BUSW *buf) {
	char	*ptr;
	int	nw = 0;

	// We'll never be called with more than MAXWRLEN words to write at once.
	// This is a configurable option length, set at the top of this file.
	// (currently set at 32, but subject to change ...)  This is important,
	// as the return channel *must* be capable of holding at least this many
	// acknowledgments in its buffer.
	//
	// assert(len <= MAXWRLEN);

	// Allocate a buffer of five bytes per word, one for addr, plus
	// len more
	bufalloc((len+2)*5);

	DBGPRINTF("WRITEV(%08x,%d,#%d,0x%08x ...)\n", a, p, len, buf[0]);

	// Encode the address
	// {{{
	ptr = encode_address(a, p);
	m_txaddr = a | (p ? 1:0); m_txaddr_set = true;
	// }}}

	while(nw < len) {
		int	ln = len-nw;
		if ((unsigned)ln > MAXWRLEN)
			ln = MAXWRLEN;

		DBGPRINTF("WRITEV-SUB(%08x%s [-> %08x],#%d,&buf[%d])\n",
			m_txaddr, (p)?"++":"", a/4+(p? nw:0), ln, nw);
		for(int i=0; i<ln; i++) { // Write one word at a time
			// {{{
			BUSW	val = buf[nw+i];
			int	ival = (int)val;

			DBGPRINTF("        WVAL: 0x%08x\n", buf[nw+i]);
			int	caddr = 0;
			// Let's try compression
			for(int j=1; j<512; j++) {
				unsigned	tstaddr;
				tstaddr = (m_wraddr - j) & 0x1ff;
				if ((!m_wrloaded)&&(tstaddr >= (unsigned)m_wraddr))
					break;
				if (m_writetbl[tstaddr] == val) {
					caddr = j & 0x1ff;
					DBGPRINTF("WR-LOOKUP, TBL[0x%03x - %d] = 0x%08x -> %3d\n", m_wraddr, j, m_writetbl[tstaddr], caddr);
					break;
				}
			}

			if (caddr > 0 && caddr <= 4) {
				DBGPRINTF("WR-ENCODING.C0 %3d\n", caddr);
				*ptr++ = 0x30 | (caddr-1);
			} else if (caddr != 0) {
				DBGPRINTF("WR-ENCODING.C1 %3d\n", caddr);
				caddr -= 1;
				*ptr++ = 0x34 | ((caddr >> 7) & 0x03);
				*ptr++ = (caddr & 0x07f);
			} else if ((ival >= -256) && (ival < 256)) {
				DBGPRINTF("WR-ENCODING.2 %10d\n", val);
				*ptr++ = 0x38|((val >> 7) & 3);
				*ptr++ = (val & 0x07f);

				// For small values like this, we don't write
				// them into the table.
			} else if ((ival >= -32768) && (ival < 32768)) {
				DBGPRINTF("WR-ENCODING.3 %10d\n", val);
				*ptr++ = 0x3c|((val >> 14) & 3);
				*ptr++ = (val >> 7) & 0x07f;
				*ptr++ = (val     ) & 0x07f;

				m_writetbl[m_wraddr++] = val;
				m_wraddr &= 0x1ff;
				if (m_wraddr == 0)
					m_wrloaded = true;
			} else {
				DBGPRINTF("WR-ENCODING.F 0x%08x\n", val);
				// Otherwise, we have to do this the hard way
				*ptr++ = 0x020 | ((val>>28)&0x0f);
				*ptr++ = (val>>21)&0x7f;
				*ptr++ = (val>>14)&0x7f;
				*ptr++ = (val>> 7)&0x7f;
				*ptr++ = (val    )&0x7f;

				m_writetbl[m_wraddr++] = val;
				m_wraddr &= 0x1ff;
				if (m_wraddr == 0)
					m_wrloaded = true;
			}

			if (p == 1) m_txaddr += 4;
			// }}}
		}

		m_dev->write(m_buf, ptr-m_buf);
assert(ptr-m_buf <= m_buflen);
		DBGPRINTF(">> ");
		for(char *tp=m_buf; tp<ptr; tp++)
			DBGPRINTF("0x%02x ", (*tp)&0x0ff);
		DBGPRINTF("\n");

		readidle();

		nw += ln;
		ptr = m_buf;
	}
	DBGPRINTF("WR: LAST TX-ADDRESS LEFT AT %08x\n", m_txaddr);

	// Need to clear the incoming queue ... if there's anything there.
	// We could do a ...
	//	readacks(len);
	// to clear a known number of acks (up to half the length of our buffer
	// which we can let just sit for speed ...), or we could do a ...
	//	readtilidle(void);
	// Then, upon startup we could also start with a readtilidle(); command.
	// This would help to clear out the problems between programs, where
	// one program doesn't finish reading, and the next gets a confusing
	// message.
	readidle();
}
// }}}

//
// writez
// {{{
// Write a buffer of values to a single address.
//
void	EXBUS::writez(const BUSW a, const int len, const BUSW *buf) {
	writev(a, 0, len, buf);
}
// }}}

//
// writei
// {{{
// Write a buffer of values to a memory range.  Unlike writez, this function
// increments the address pointer after every memory write.
//
void	EXBUS::writei(const BUSW a, const int len, const BUSW *buf) {
	writev(a, 1, len, buf);
}
// }}}

//
// readio
// {{{
// Read a single value from the bus.
//
// If the bus returns an error, this routine will print a comment and throw
// the error up the chain.  If the address of the value read doesn't match
// the address requested (an internal check), then an error message will be
// sent to the log file and the interface will exit with an error condition.
// This should only happen if there are bugs in the interface, and hopefully
// I've gotten rid of all of those.
//
EXBUS::BUSW	EXBUS::readio(const EXBUS::BUSW a) {
	BUSW	v;

	// I/O reads are now the same as vector reads, but with a vector length
	// of one.
	DBGPRINTF("READIO(0x%08x)\n", a);
	try {
		readv(a, 0, 1, &v);
	} catch(BUSERR b) {
		DBGPRINTF("BUSERR trying to read %08x\n", a);
		throw BUSERR(a);
	}

	if (m_rxaddr != a) {
		DBGPRINTF("LAST-ADDR MIS-MATCH: (RCVD) %08x != %08x (XPECTED)\n", m_rxaddr, a);
		m_rxaddr_set = false;
		m_txaddr_set = false;

		// throw BUSERR(a);
	}

	DBGPRINTF("READIO(0x%08x) <= 0x%08x\n", a, v);
	return v;
}
// }}}

//
// encode_address
// {{{
// Creates a message to be sent across the bus with a new address value
// in it.
//
char	*EXBUS::encode_address(const EXBUS::BUSW a, const bool inc) {
	EXBUS::BUSW	addr = a;
	char	*sbuf = m_buf, *ptr = m_buf;
	int	diffaddr = ((a&-2) - (m_txaddr & -2))>>2;

	// Sign extend the difference address
	diffaddr <<= 2; diffaddr >>= 2;

	// Double check that we are aligned
	if ((a&3)!=0) {
		DBGPRINTF("ERROR: Address is unaligned\n");
		throw BUSERR(a);
	} if (inc)
		addr |= 1;

	if ((m_txaddr_set)&&((addr | (inc ? 1:0)) == m_txaddr))
		return ptr;

	if (m_txaddr_set) { // Diff. address
		// {{{

		if ((diffaddr >= -2)&&(diffaddr < 2)) {
			if (diffaddr == 1)		// 0100
				*ptr = 0x12;
			else if (diffaddr == -1)	// 1100
				*ptr = 0x16;
			else if (diffaddr == -2)	// 1000
				*ptr = 0x14;
			else // if (diffaddr ==  0)	// 0000
				*ptr =  0x10;

			if (inc)
				*ptr |= 1;
			ptr++;
		} else if ((diffaddr >= -(1<<6))&&(diffaddr < (1<<6))) {
			*ptr++ = 0x1a | ((diffaddr < 0) ? 1:0);	// SGN bit
			*ptr   = (diffaddr << 1) & 0x07e;	// 6b
			if (inc)
				*ptr |= 1;			// 1b for INC
			ptr++;
		} else if ((diffaddr >= -(1<<13))&&(diffaddr < (1<<13))) {
			*ptr++ = 0x1e | ((diffaddr < 0) ? 1:0);	// SGN bit
			*ptr++ = (diffaddr >> 6) & 0x07f;	// 7b
			*ptr   = (diffaddr << 1) & 0x07e;	// 6b
			if (inc)
				*ptr |= 1;			// 1b for INC
			ptr++;
		}
		*ptr = '\0';

#ifdef	EXDEBUG
		DBGPRINTF("DIF-ADDR: (%ld) encodes last_addr(0x%08x) %6d(0x%06x):",
			ptr-sbuf,
			m_txaddr,
			diffaddr, diffaddr&0x0fffff);
		for(char *sptr = sbuf; sptr < ptr; sptr++)
			DBGPRINTF("%02x ", (uint32_t)*sptr);
		DBGPRINTF("\n");
#endif
	}
	// }}}

	// Encode an absolute (low memory) address (if "better")
	// {{{
	{
		// Prefer absolute address encoding over differential encoding,
		// when both encodings encode the same address, and when both
		// encode the address in the same number of words
		int	waddr = ((int)addr) >> 2;

		if ((waddr >= -(1<<7))&&(waddr < 1<<7)
				&&((ptr == sbuf)||(ptr >= &sbuf[2]))) {
			DBGPRINTF("Setting ADDR.1 to %08x\n", addr);
			ptr = sbuf;
			*ptr++ = 0x18 | ((waddr  < 0) ? 1:0);
			*ptr   = ( waddr << 1) & 0x07e;
			if (inc)
				*ptr |= 1;
			ptr++;
		} else if (((waddr >= -1<<13)&&(waddr < 1<<13))
				&&((ptr == sbuf)||(ptr >= &sbuf[3]))) {
			DBGPRINTF("Setting ADDR.2 to %08x\n", addr);
			ptr = sbuf;
			*ptr++ = 0x1c | ((waddr  < 0) ? 1:0);
			*ptr++ = ( waddr >> 6) & 0x07f;
			*ptr   = ( waddr << 1) & 0x07e;
			if (inc)
				*ptr |= 1;
			ptr++;
		} else if (ptr == sbuf) { // Send our full/raw/complete address
			DBGPRINTF("Setting ADDR.F to %08x\n", addr);
			ptr = sbuf;
			*ptr++ = ((addr>>28) & 0x00f) | 0;
			*ptr++ = ( addr>>21) & 0x07f;
			*ptr++ = ( addr>>14) & 0x07f;
			*ptr++ = ( addr>> 7) & 0x07f;
			*ptr   = ( addr    ) & 0x07c;
			if (inc)
				*ptr |= 1;
			ptr++;
		}
	}
	// }}}

	*ptr = '\0';
#ifdef	EXDEBUG
	DBGPRINTF("ADDR-CMD%2s%2s: (%ld) ", (m_txaddr_set) ? "/S":"", (inc) ? "/I":"", ptr-sbuf);
	for(int k=0; k<ptr-sbuf; k++)
		DBGPRINTF("%02x%s", sbuf[k] & 0x0ff, (k+1 < ptr-sbuf)?":":"");
	if (m_txaddr_set)
		DBGPRINTF("\tDIF=0x%08x", diffaddr);
	DBGPRINTF("\n");
#endif
	// m_rdaddr = 0;

	return ptr;
}
// }}}

// readcmd -- Generate a read command to read up to 17+2048 items
// {{{
char	*EXBUS::readcmd(const int len, char *buf) {
	char	*ptr = buf;

	DBGPRINTF("READCMD: LEN = %d: ", len);
	assert(len <= 2064);
	assert(len > 0);

	if (len <= 16) {
		*ptr++ = 0x40 | ((len - 1) & 0x0f);
		DBGPRINTF("%02x\n", ptr[-1] & 0x0ff);
	} else {
		unsigned	pln = len-17;
		*ptr++ = 0x50 |((pln >> 7) & 0x0f);
		*ptr++ = (pln & 0x7f);
		DBGPRINTF("%02x:%02x\n", ptr[-2] & 0x0ff, ptr[-1] & 0x0ff);
	}

	return ptr;
}
// }}}

//
// readv
// {{{
// This is the main worker routine for read calls.  readio, readz, readi, all
// end up here.  readv() reads a buffer of data from the given address, and
// optionally increments (or not) the address after every read.
//
// Parameters:
//	a	The address to start reading from
//	inc	'1' if we want to increment the address following each read,
//		'0' otherwise
//	len	The number of words to read
//	buf	A memory buffer storage location to place the results into
//
void	EXBUS::readv(const EXBUS::BUSW a, const int inc, const int len, EXBUS::BUSW *buf) {
	const	int	READAHEAD = MAXRDLEN/2, READBLOCK=(MAXRDLEN/2>512)?512:MAXRDLEN/2;
	int	cmdrd = 0, nread = 0;
	// EXBUS::BUSW	addr = a;
	char	*ptr = m_buf;

	if (len <= 0)
		return;
	DBGPRINTF("READV(%08x,%d,#%4d)\n", a, inc, len);

	ptr = encode_address(a, inc);
	m_txaddr_set = true; m_txaddr = a | (inc ? 1:0);
	try {
		while(cmdrd < len) {
			// ptr = m_buf;
			do {
				int	nrd = len-cmdrd;
				if (nrd > READBLOCK)
					nrd = READBLOCK;
				if (cmdrd-nread + nrd>READAHEAD+READBLOCK)
					nrd = READAHEAD+READBLOCK-(cmdrd-nread);
				ptr = readcmd(nrd, ptr);
				cmdrd += nrd;
				if (inc)
					m_txaddr += 4*nrd;
			} while((cmdrd-nread
				< READAHEAD+READBLOCK)&&(cmdrd< len));

			m_dev->write(m_buf, (ptr-m_buf));

			// DBGPRINTF("Reading %d words\n", (cmdrd-nread));
			while(nread<(cmdrd-READAHEAD)) {
				buf[nread++] = readword();
			} ptr = m_buf;
		} DBGPRINTF("Reading %d words, to end the read\n", len-nread);
		while(nread<len) {
			buf[nread++] = readword();
		}
	} catch(BUSERR b) {
		DBGPRINTF("READV::BUSERR trying to read %08x\n", a+((inc)?nread:0));
		throw BUSERR(a+((inc)?(nread<<2):0));
	}

	/*
	if ((unsigned)m_lastaddr != (a+((inc)?(len<<2):0))) {
		DBGPRINTF("EXBUS::READV(a=%08x,inc=%d,len=%4x,x) ERR: (Last) %08x != %08x + %08x (Expected)\n", a, inc, len<<2, m_lastaddr, a, (inc)?(len<<2):0);
		printf("EXBUS::READV(a=%08x,inc=%d,len=%4x,x) ERR: (Last) %08x != %08x + %08x (Expected)\n", a, inc, len<<2, m_lastaddr, a, (inc)?(len<<2):0);
		sleep(1);
		assert((int)m_lastaddr == (a+(inc)?(len<<2):0));
		exit(-3);
	}
	*/

	DBGPRINTF("READV::COMPLETE\n");
}
// }}}

//
// readi
// {{{
// Read a series of values from bus addresses starting at address a,
// incrementing the address to read from subsequent addresses along the way.
//
// Works by just calling readv to do the heavy lifting.
//
void	EXBUS::readi(const EXBUS::BUSW a, const int len, EXBUS::BUSW *buf) {
	readv(a, 1, len, buf);
}
// }}}

//
// readz
// {{{
// Read a series of values from the bus, with all the values coming from the
// same address: a.  The address is not incremented between individual word
// reads.
//
// Also calls readv to do the heavy lifting.
//
void	EXBUS::readz(const EXBUS::BUSW a, const int len, EXBUS::BUSW *buf) {
	readv(a, 0, len, buf);
}
// }}}

//
// readword()
// {{{
// Once the read command has been issued, readword() is called to read each
// word's response from the bus.  This also processes any out of bounds
// characters, such as interrupt notifications or bus error condition
// notifications.
//
EXBUS::BUSW	EXBUS::readword(void) {
	EXBUS::BUSW	val = 0;
	int		nr;

	DBGPRINTF("READ-WORD()\n");

	// We know we need to read at least one word, so let's get that
	// first byte which tells us what follows.
	do {
		do {
			nr = lclreadcode(&m_buf[0], 1);
		} while (nr < 1);

		// Keep waiting for a read result
		// DBGPRINTF("First byte: %02x\n", m_buf[0]);

		// Read the rest of the return word.  This is necessary
		//   to keep us synchronized
		val = readrest();

		// However ... it might not be a read return, so ignore
		//   anything else.
	} while((m_buf[0] & 0x60) != 0x20);

	return val;
}
// }}}

//
// readrest()
// {{{
// Once the read command has been issued, readword() is called to read each
// word's response from the bus.  This also processes any out of bounds
// characters, such as interrupt notifications or bus error condition
// notifications.
//
EXBUS::BUSW	EXBUS::readrest(void) {
	EXBUS::BUSW	val = 0;
	int		nr;
	unsigned	sbyte, rdaddr;

	sbyte = m_buf[0];
	nr = 1;
DBGPRINTF("Read-rest from %02x\n", sbyte & 0x0ff);

	if (0 && (sbyte & 0x060) == 0x60) {
		// Specials
		// {{{
		m_gpio = (sbyte >> 3) & 0x03;
		switch(sbyte & 0x07) {
		case 0x00: // Reset design request
			DBGPRINTF("READWORD::Reset design ACK\n");
			break;
		case 0x01: // Reset bridge request
			DBGPRINTF("READWORD::Reset bridge ACK\n");
			break;
		case 0x02: // Bus error
			m_bus_err = true;
			DBGPRINTF("READWORD::BUSRESET (unknown addr)\n");
			throw BUSERR(0);
			break;
		case 0x03: // FIFO overflow
			DBGPRINTF("READWORD::FIFO OVERFLOW!!\n");
			// throw BUSERR(0);
			break;
		default:
			DBGPRINTF("READWORD::(Other special)\n");
			if (sbyte & 0x01)
				m_interrupt_flag = true;
			break;
		}

		// Otherwise ignore any Idle's (for now)
		// }}}
	} else if ((sbyte & 0x060) == 0x20) {
		// Read return
		if ((sbyte & 0x070) == 0x20) {
			// {{{
			// Full word return
			do {
				nr += lclreadcode(&m_buf[nr], 5-nr);
			} while (nr < 5);

			val  = (m_buf[4] & 0x7f);
			val |= (m_buf[3] & 0x7f) <<  7;
			val |= (m_buf[2] & 0x7f) << 14;
			val |= (m_buf[1] & 0x7f) << 21;
			val |= (m_buf[0] & 0x7f) << 28;

			DBGPRINTF("READ-WORD() -- FULL-READ %02x:%02x:%02x:%02x:%02x -- %08x, A=%08x --> TBL[%04x]\n",
				m_buf[0], m_buf[1], m_buf[2], m_buf[3],
				m_buf[4], val, m_rxaddr & -2, m_rdaddr);

			m_readtbl[m_rdaddr++] = val; m_rdaddr &= 0x01ff;
			m_quiktbl[m_qkaddr++] = val; m_qkaddr &= 3;
			// }}}
		} else if ((sbyte & 0x07c) == 0x30) {
			// {{{
			unsigned	idx;

			idx = (m_buf[0] & 0x03);
			rdaddr = (m_qkaddr - idx - 1) & 0x03;
			val = m_quiktbl[rdaddr];
			DBGPRINTF("READ-WORD() -- quick table value[0x%04x-%3d=0x%04x], %08x, A=%08x\n", m_qkaddr, idx, rdaddr, val, m_rxaddr & -2);
			// Since the item was found in the quick table, it
			//   doesn't need to go back into the quick table,
			//   lest we fill up the quick table with all identical
			//   values and thus lose its effectiveness.
			// m_quiktbl[m_qkaddr++] = val; m_qkaddr &= 3;
			// }}}
		} else if ((sbyte & 0x07c) == 0x34) {
			// {{{
			unsigned	idx;

			do {
				nr += lclreadcode(&m_buf[nr], 2-nr);
			} while (nr < 2);

			idx  = (m_buf[1] & 0x7f);
			idx |= (m_buf[0] & 0x03) << 7;
			rdaddr = (m_rdaddr - idx - 1) & 0x01ff;
			val = m_readtbl[rdaddr];
			DBGPRINTF("READ-WORD() -- long table value[%3d], %08x, A=%08x\n", idx, val, m_rxaddr & -2);
			m_quiktbl[m_qkaddr++] = val; m_qkaddr &= 3;
			// }}}
		} else if ((sbyte & 0x07c) == 0x38) {
			// {{{
			// Small value return
			do {
				nr += lclreadcode(&m_buf[nr], 2-nr);
			} while (nr < 2);

			val  = (m_buf[1] & 0x7f);
			val |= (m_buf[0] & 0x7f) <<  7;

			// Sign extend val
			val <<= (sizeof(BUSW)*8 - 9);
			val = ((int)val >> (sizeof(BUSW)*8 - 9));


			DBGPRINTF("READ-WORD() -- SMALL-READ %02x:%02x -- %08x, A=%08x\n",
			m_buf[0], m_buf[1], val, m_rxaddr & -2);
			m_quiktbl[m_qkaddr++] = val; m_qkaddr &= 3;
			// }}}
		} else if ((sbyte & 0x07c) == 0x3c) {
			// {{{
			// Medium value return
			do {
				nr += lclreadcode(&m_buf[nr], 3-nr);
			} while (nr < 3);

			val  = (m_buf[2] & 0x7f);
			val |= (m_buf[1] & 0x7f) <<  7;
			val |= (m_buf[0] & 0x03) << 14;

			// Sign extend val
			val <<= (sizeof(BUSW)*8 - 16);
			val = ((int)val >> (sizeof(BUSW)*8 - 16));


			DBGPRINTF("READ-WORD() -- MEDIUM-READ %02x:%02x:%02x -- %08x, A=%08x --> TBL[0x%04x]\n",
				m_buf[0], m_buf[1], m_buf[2], val,
				m_rxaddr & -2, m_rdaddr);

			m_readtbl[m_rdaddr++] = val; m_rdaddr &= 0x01ff;
			m_quiktbl[m_qkaddr++] = val; m_qkaddr &= 3;
			// }}}
		}

		if (m_rxaddr_set && (m_rxaddr & 1))
			m_rxaddr += 4;

		return val;
	} else if ((sbyte & 0x060) == 0x40) {
		// Write acknowledgment -- ignore it here
		if (m_rxaddr_set && (m_rxaddr & 1))
			m_rxaddr += (1+(sbyte & 0x1f)) * 4;
	} else if ((sbyte & 0x060) == 0x00) {
		// Address acknowledgment
DBGPRINTF("Address ACK: RxAddr = %08x%s\n", m_rxaddr, m_rxaddr_set ? "":"\t(Unknown)");
		// {{{
		if ((sbyte & 0x070) == 0x00) {
			// {{{
			do {
				nr += lclreadcode(&m_buf[nr], 5-nr);
			} while (nr < 5);

			val  = (m_buf[4] & 0x7f);
			val |= (m_buf[3] & 0x7f) <<  7;
			val |= (m_buf[2] & 0x7f) << 14;
			val |= (m_buf[1] & 0x7f) << 21;
			val |= (m_buf[0] & 0x7f) << 28;

			m_rxaddr_set = true;
			m_rxaddr = val;

			DBGPRINTF("RCVD ADDR/5: 0x%08x\n", val);
			// }}}
		} else if ((sbyte & 0x01c) == 0x18) {
			// {{{
			do {
				nr += lclreadcode(&m_buf[nr], 2-nr);
			} while (nr < 2);

			val  = (m_buf[1] & 0x07f);
			val |= (m_buf[0] & 0x07f) << 7;

			// Sign extend val
			val <<= (sizeof(BUSW)*8 - 8);
			val = ((int)val >> (sizeof(BUSW)*8 - 10));

			if (m_buf[0] & 0x02)
				// Signed displacement
				m_rxaddr += val;
			else {
				m_rxaddr = val;
				m_rxaddr_set = true;
			}

			if (m_rxaddr_set)
				DBGPRINTF("RCVD ADDR/2: %s0x%08x (val = %08x)\n",
					(m_buf[0] & 0x02) ? "+":" ",
					m_rxaddr, val);
			// }}}
		} else if ((sbyte & 0x01c) == 0x1c) {
			// {{{
			do {
				nr += lclreadcode(&m_buf[nr], 3-nr);
			} while (nr < 3);

			val  = (m_buf[2] & 0x07f);
			val |= (m_buf[1] & 0x07f) << 7;
			val |= (m_buf[0] & 0x07f) << 14;

DBGPRINTF("VAL: %02x:%02x:%02x -- %08x\n", m_buf[0] & 0x0ff, m_buf[1] & 0x0ff, m_buf[2] & 0x0ff, val);

			// Sign extend val
			val <<= (sizeof(BUSW)*8 - 15);
			val = ((int)val >> (sizeof(BUSW)*8 - 17));

			if (m_buf[0] & 0x02)
{
				// Signed displacement
				m_rxaddr += val;
DBGPRINTF("ADDR-DISPLACEMENT: %08x\n", val);
}
			else {
				m_rxaddr = val;
				m_rxaddr_set = true;
			}

			if (m_rxaddr_set)
				DBGPRINTF("RCVD ADDR/3: %s0x%08x\n",
					(m_buf[0] & 0x02) ? "+":" ",
					m_rxaddr);
			// }}}
		} else {
			// {{{
			val = m_buf[0] & 0x07;
			val <<= (sizeof(BUSW)*8-3);
			val = ((int)val >> (sizeof(BUSW)*8 - 5));

			// Signed displacement
			m_rxaddr += val;

			if (m_rxaddr_set)
				DBGPRINTF("RCVD ADDR/1: 0x%08x\n", m_rxaddr);
			// }}}
		}
		// }}}
	}

	return val;
}
// }}}

//
// readidle()
// {{{
// Reads until the bus becomes idle.  This is called by writev to make sure
// any write acknowledgements are sufficiently flushed from the stream.  In
// case anything else is in the stream ... we mostly ignore that here too.
//
void	EXBUS::readidle(void) {
	int		nr;

	DBGPRINTF("READ-IDLE()\n");

	while((m_dev->available())&&((nr=lclreadcode(&m_buf[0], 1))>0))
		readrest();
}
// }}}

//
// sync()
// {{{
void	EXBUS::sync(void) {
	int	nr, sync_count;
	char	syncbuf[6];

	syncbuf[0] = 0x61;
	for(int k=1; k<6; k++)
		syncbuf[k] = 0x66;
	m_dev->write(syncbuf, 6);

	DBGPRINTF("Waiting on sync ...\n");
	sync_count = 0;
	do {
		nr = lclreadcode(syncbuf, 1);
		if (nr == 1) {
			if (0x64 == (syncbuf[0] & 0x64))
				sync_count++;
			else
				sync_count = 0;
		}
	} while(sync_count < 5);
	DBGPRINTF("SYNC\'D!!\n");
}
// }}}

//
// usleep()
// {{{
// Called to implement some form of time-limited wait on a response from the
// bus.
//
void	EXBUS::usleep(unsigned ms) {
	unsigned	sbyte;

	if (m_dev->poll(ms)) {
		int	nr;
		nr = m_dev->read(m_buf, 1);
		if (nr == 0) {
			// Connection closed, let it drop
			DBGPRINTF("Connection closed!!\n");
			m_dev->close();
			exit(-1);
		} sbyte = m_buf[0];
		if ((sbyte & 0x60) != 0x60) {
			readrest();
		} else {
			if ((sbyte & 0x05)==0x05) {
				m_interrupt_flag = true;
				DBGPRINTF("!!!!!!!!!!!!!!! ----- INTERRUPT!\n");
			} if ((sbyte & 0x02) == 0x02)
				DBGPRINTF("Bus error\n");
			if ((sbyte & 0x06) == 0)
				DBGPRINTF("Bus was RESET!\n");
		}
	}
}
// }}}

//
// wait()
// {{{
// Wait for an interrupt condition.
//
void	EXBUS::wait(void) {
	if (m_interrupt_flag)
		DBGPRINTF("INTERRUPTED PRIOR TO WAIT()\n");
	do {
		usleep(200);
	} while(!m_interrupt_flag);
}
// }}}
