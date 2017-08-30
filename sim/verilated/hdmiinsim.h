#ifndef	HDMIINSIM_H
#define	HDMIINSIM_H

#include <stdio.h>
#include <stdint.h>

class	HDMIINSIM {
	typedef	uint32_t	PIXEL;

	unsigned	m_npix, m_index;
	PIXEL		*m_rawframe;

	unsigned rotate(const unsigned, const int);
public:
	HDMIINSIM(const char *fname, unsigned npix);

	HDMIINSIM(void) {
		delete[]	m_rawframe;
	}

	void	operator()(unsigned &r, unsigned &g, unsigned &b);

};

#endif
