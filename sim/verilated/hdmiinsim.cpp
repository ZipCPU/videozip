#include <stdio.h>
#include <assert.h>
#include "hdmiinsim.h"

HDMIINSIM::HDMIINSIM(const char *fname, unsigned npix) {
	fprintf(stderr, "HDMIINSIM: Opening %s\n", fname);
	FILE	*fp = fopen(fname, "rb");
	assert(fp);

	m_npix = npix;
	m_rawframe = new PIXEL[m_npix];
	size_t nr = fread(m_rawframe, sizeof(PIXEL), m_npix, fp);
	if (nr < m_npix) {
		m_npix = nr;
		fprintf(stderr, "HDMIINSIM: ERR Only %d pixels read of %d requested!\n",
			m_npix, npix);
	} fclose(fp);
	m_index = 0;
}

unsigned HDMIINSIM::rotate(const unsigned value, const int amount) {
	unsigned	r, v;
	const int	NBITS=10;

	v  = value & ((1<<NBITS)-1);
	r  = (v   >> amount);
	r |= (v   << (NBITS-amount));
	r &= ((1u <<  NBITS)-1);
	return r;
}

void	HDMIINSIM::operator()(unsigned &r, unsigned &g, unsigned &b) {
	PIXEL	pix;

	pix   = m_rawframe[m_index++];

	if (m_index >= m_npix) {
		fprintf(stderr, "FRAME!\n");
		m_index = 0;
	}
	r = (pix >> 20) & 0x03ff;
	g = (pix >> 10) & 0x03ff;
	b =  pix        & 0x03ff;
}

