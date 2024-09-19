////////////////////////////////////////////////////////////////////////////////
//
// Filename:	monitor.c
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
// Copyright (C) 2024, Gisselquist Technology, LLC
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

#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <zipcpu.h>
#include <zipsys.h>
#include "board.h"

const	unsigned NLINES=23, WIDTH=79;
char	**grid;
unsigned	m_xpos = 0, m_ypos = 0, changed=0;

__attribute__((noinline))
void	mvaddstr(int y, int x, char *str) {
	// {{{
	unsigned	sln;

	if ((x >= WIDTH)||(y<0)||(y >= NLINES))
		return;
	sln = strnlen(str, WIDTH-x);
	m_xpos = x;
	if (0 != strncmp(grid[y]+m_xpos, str, sln)) {
		strncpy(grid[y]+m_xpos, str, sln);
		changed = 1;
	}

	m_xpos += sln;
	m_ypos = y;
}
// }}}

__attribute__((noinline))
void	mvprintw(int y, int x, char *fmt, ...) {
	// {{{
	char	str[WIDTH];
	va_list	va;

	if ((x >= WIDTH)||(y<0)||(y >= NLINES))
		return;
	va_start(va, fmt);
	m_xpos = x;
	vsnprintf(str, sizeof(str), fmt, va);
	mvaddstr(y, x, str);
	va_end(va);
}
// }}}

void	redrawwin(void) {
	// {{{
	unsigned	y;

	for(y=0; y<NLINES; y++) {
		char	ch, *eol;
		eol = &grid[y][WIDTH];
		ch = *eol; *eol = '\0';
		puts(grid[y]);	// Includes a line feed at the end
		*eol = ch;
	}

	changed = 0;
}
// }}}

void	clear(void) {
	// {{{
	unsigned	k, y;
	char	str[WIDTH];

	for(k=0; k<WIDTH; k++)
		str[k] = ' ';
	for(y=0; y<NLINES; y++) {
		if (0 != strncmp(grid[y], str, WIDTH)) {
			strncpy(grid[y], str, WIDTH);
			changed = 1;
		}
	}
}
// }}}

void	update_spio(int yp, int xp) {
	// {{{
#ifdef	_BOARD_HAS_SPIO
	unsigned spiov = *_spio;

	// Buttons
	mvaddstr(yp+0,xp+ 8, (spiov & 0x010000) ? "1":"0");
	mvaddstr(yp+1,xp+10, (spiov & 0x020000) ? "1":"0");
	mvaddstr(yp+1,xp+ 6, (spiov & 0x040000) ? "1":"0");
	mvaddstr(yp+2,xp+ 8, (spiov & 0x080000) ? "1":"0");
	mvaddstr(yp+1,xp+ 8, (spiov & 0x100000) ? "1":"0");

	// LEDs
	if (spiov & 0x1000000) {
		//		0 0 0 0   0 0 0 0"
		mvaddstr(yp+3,xp+ 0, " Knight - Rider");
	} else {
		mvaddstr(yp+3,xp+ 0, (spiov & 0x080) ? "!":" ");
		mvaddstr(yp+3,xp+ 2, (spiov & 0x040) ? "!":" ");
		mvaddstr(yp+3,xp+ 4, (spiov & 0x020) ? "!":" ");
		mvaddstr(yp+3,xp+ 6, (spiov & 0x010) ? "!":" ");
		//
		mvaddstr(yp+3,xp+10, (spiov & 0x008) ? "!":" ");
		mvaddstr(yp+3,xp+12, (spiov & 0x004) ? "!":" ");
		mvaddstr(yp+3,xp+14, (spiov & 0x002) ? "!":" ");
		mvaddstr(yp+3,xp+16, (spiov & 0x001) ? "!":" ");
	}

	// Switches
	mvaddstr(yp+4,xp+ 0, (spiov & 0x08000) ? "1":"0");
	mvaddstr(yp+4,xp+ 2, (spiov & 0x04000) ? "1":"0");
	mvaddstr(yp+4,xp+ 4, (spiov & 0x02000) ? "1":"0");
	mvaddstr(yp+4,xp+ 6, (spiov & 0x01000) ? "1":"0");
	//
	mvaddstr(yp+4,xp+10, (spiov & 0x00800) ? "1":"0");
	mvaddstr(yp+4,xp+12, (spiov & 0x00400) ? "1":"0");
	mvaddstr(yp+4,xp+14, (spiov & 0x00200) ? "1":"0");
	mvaddstr(yp+4,xp+16, (spiov & 0x00100) ? "1":"0");
#endif
}
// }}}

void	update_gpio(int yp, int xp) {
	// {{{
#ifdef	_BOARD_HAS_GPIO
	unsigned gpiov = *_gpio;
	mvprintw(yp+0,xp+ 0, "Outputs: %04x", gpiov &0x0ffff);
	mvprintw(yp+0,xp+40, "Inputs:  %04x", (gpiov >> 16)&0x0ffff);
	mvaddstr(yp+1,xp+ 0, "------------------------------");
	mvaddstr(yp+1,xp+40, "------------------------------");

	mvprintw(yp+2,xp+ 1, "%-20s", (gpiov & GPIO_HDMIRX_TXEN) ? "HDMI RX TXEN":"");
	mvprintw(yp+3,xp+ 1, "%-20s", (gpiov & 0x08) ? "HDMI RX HPA":"");
	mvprintw(yp+4,xp+ 1, "%-20s", (gpiov & 0x20) ? "OLED-RESET":"");
	mvprintw(yp+5,xp+ 1, "%-20s", (gpiov & 0x40) ? "OLED PANEL EN":"");
	mvprintw(yp+6,xp+ 1, "%-20s", (gpiov & 0x80) ? "OLED LOGIC EN":"");
	// mvprintw( 9,xp+ 1, "%-20s", (gpiov & 0x01) ? "HDMI-RX CEC":"");
	// mvprintw(10,xp+ 1, "%-20s", (gpiov & 0x02) ? "HDMI-TX CEC":"");
	// mvprintw(11, 1, "%-20s", (gpiov & 0x10) ? "":"SD-RESET");

	// mvprintw( 9,xp+41,"%-20s",(gpiov & 0x010000)? "HDMI-RX CEC":"");
	// mvprintw(10,xp+41,"%-20s",(gpiov & 0x020000)? "HDMI-TX CEC":"");
	// mvprintw(11,xp+41, "%-20s", (gpiov & 0x040000) ? "HDMI TX EN":"");
	// mvprintw(14,xp+41, "%-20s", (gpiov & 0x200000) ? "GPS 3DF":"");
	mvprintw(yp+2,xp+41,"%-20s", (gpiov & GPIO_SD_DETECTED) ? "SD Card detect":"");
	mvprintw(yp+3,xp+41,"%-20s", (gpiov & GPIO_HDMITX_DETECT) ? "HDMI-TX Hotplug det":"");
	mvprintw(yp+4,xp+41,"%-20s", (gpiov & GPIO_SYSCLK_LOCKED) ? "SYSCLK Locked":"");
	mvprintw(yp+5,xp+41,"%-20s", (gpiov & GPIO_VIDCLK_LOCKED) ? "PXRX Clk locked":"");
#endif
}
// }}}

void	clkout(int y, int x, char *str, unsigned v) {
	// {{{
	double hz = v;

	if (hz < 1e3)
		mvprintw(y, x, "%12s:       %3.0f Hz", str, hz);
	else if (hz < 1e6)
		mvprintw(y, x, "%12s:    %7.3f kHz", str, hz / 1000.0);
	else
		mvprintw(y, x, "%12s: %8.2f MHz", str, hz / 1e6);
}
// }}}

void	update_clocks(int yp, int xp) {
	// {{{
	mvaddstr(yp+0,xp+ 0, "Clocks:");
	mvaddstr(yp+1,xp+ 0, "------------------------------");
	clkout(yp+2,xp+1, "Network RX", *_netclockctr);
	clkout(yp+3,xp+1, "Network TX", *_nettxctr);
	clkout(yp+4,xp+1, "HDMI RX", _hdmi->v_hdmifreq);
	clkout(yp+5,xp+1, "HDMI TX", _hdmi->v_pxfreq);
}
// }}}

void	update_net(int yp, int xp) {
	// {{{
#ifdef	_BOARD_HAS_MEGANET
	mvaddstr(yp+0,xp+0, "Network:");
	mvaddstr(yp+1,xp+0, "------------------------------");
	mvprintw(yp+2,xp+1, "%13s %7d/%7d", "Packets:", _net->n_rxpkt & 0x0fffffff, _net->n_txpkt);
	mvprintw(yp+3,xp+1, "%13s %7d/%7d", "ARP Packets:",  _net->n_rxarp, _net->n_txarp);
	mvprintw(yp+4,xp+1, "%13s %7d/%7d", "ICMP Packets:", _net->n_rxicmp, _net->n_txicmp);
	// mvaddstr(yp+5,xp+1,"%13s %7d/%7d", "CPU Packets:",  0, 0);
#endif
}
// }}}

void	update_video(int yp, int xp) {	// yp+0, xp+40
	// {{{
#ifdef	_BOARD_HAS_VIDPIPE
	unsigned	vpipe;

	vpipe = _hdmi->v_control;
	mvaddstr(yp+0,xp+ 0, "HDMI:");
	mvaddstr(yp+1,xp+ 0, "------------------------------");

	if (vpipe & 1) {
		mvprintw(yp+0,xp+10, "%-30s","Reset");
		mvprintw(yp+2,xp+ 1, "%-20s","Size:");
		mvprintw(yp+3,xp+ 1, "%-20s","Porch:");
		mvprintw(yp+4,xp+ 1, "%-20s","Sync:");
		mvprintw(yp+5,xp+ 1, "%-20s","Raw:");
		mvprintw(yp+2,xp+22, "%-20s","FPS:");
		mvprintw(yp+3,xp+22, "%-20s","Sync:");
	} else {
		unsigned	syncw;

		syncw = _hdmi->v_syncword;

		if (0 == (vpipe & 0x020))
			mvaddstr(yp+0,xp+10, "CLK: Lcl");
		else if (0x20 == (vpipe & 0x020))
			mvaddstr(yp+0,xp+10, "CLK: RX ");

		if (0 == (vpipe & 0x040))
			mvprintw(yp+0,xp+20, "%-12s","[Local]");
		else // if (0x40 == (vpipe & 0x040))
			mvprintw(yp+0,xp+20, "%-12s","External");

		if (0 == (_hdmi->v_syncword & 0x1000000)
			||(vpipe & 0x040)) { // If SYNCd or External

			mvprintw(yp+2,xp+ 1, "xSize:  %4d x %4d",	// 18ch
				_hdmi->v_in.m_height, _hdmi->v_in.m_width);
			mvprintw(yp+3,xp+ 1, "xPorch: %4d x %4d",
				_hdmi->v_in.m_vporch, _hdmi->v_in.m_hporch);
			mvprintw(yp+4,xp+ 1, "xSync:  %4d x %4d",
				_hdmi->v_in.m_vsync, _hdmi->v_in.m_hsync);
			mvprintw(yp+5,xp+ 1, "xRaw:   %4d x %4d",
				_hdmi->v_in.m_raw_height, _hdmi->v_in.m_raw_width);
		} else {
			mvprintw(yp+2,xp+ 1, "LSize:  %4d x %4d",	// 18ch
				_hdmi->v_src.m_height, _hdmi->v_src.m_width);
			mvprintw(yp+3,xp+ 1, "LPorch: %4d x %4d",
				_hdmi->v_src.m_vporch, _hdmi->v_src.m_hporch);
			mvprintw(yp+4,xp+ 1, "LSync:  %4d x %4d",
				_hdmi->v_src.m_vsync, _hdmi->v_src.m_hsync);
			mvprintw(yp+5,xp+ 1, "LRaw:   %4d x %4d",
				_hdmi->v_src.m_raw_height, _hdmi->v_src.m_raw_width);
		}

		mvprintw(yp+2,xp+22, "FPS:  0x%08x", _hdmi->v_fps);
		mvprintw(yp+3,xp+22, "SYNC: 0x%08x", _hdmi->v_syncword);
		mvprintw(yp+4,xp+24, "%-10s", (_hdmi->v_syncword & 0x1000000)
				? "(No sync)":"Locked");
		mvaddstr(yp+5,xp+22, "CMAP: ");
		switch(vpipe & 0x700) {
		case 0x000: mvprintw(yp+5,xp+27,"%-12s","1b B/W"); break;
		case 0x100: mvprintw(yp+5,xp+27,"%-12s","2b Gray"); break;
		case 0x200: mvprintw(yp+5,xp+27,"%-12s","4b Colormap"); break;
		case 0x300: mvprintw(yp+5,xp+27,"%-12s","8b Colormap"); break;
		case 0x400: mvprintw(yp+5,xp+27,"%-12s"," 8b Color"); break;
		case 0x500: mvprintw(yp+5,xp+27,"%-12s","16b Color"); break;
		case 0x600: mvprintw(yp+5,xp+27,"%-12s","24b Packed"); break;
		case 0x700: mvprintw(yp+5,xp+27,"%-12s","24b Color"); break;
		default:    mvprintw(yp+5,xp+27,"%-12s","(Unknown)"); break;
		}
		mvprintw(yp+6,xp+22, "ALPH: %1d", (vpipe >> 14)&3);
		mvprintw(yp+6,xp+30, "%-4s", ((vpipe >> 17)&1) ? "ERR":"");
	}

	mvprintw(yp+6,xp+ 1, "%-7s 0x%08x","VidPipe:", vpipe);
#endif
}
// }}}

void	update(void) {
	// {{{
	mvprintw(0, 0, "Version: %08x", *_version);
	mvprintw(0,20, "BuildTime: %06x", *_buildtime & 0x0ffffff);

	update_spio(1,0);
	update_gpio(7,0);
	update_clocks(16,0);
	update_net(16,40);
	update_video(0,40);
}
// }}}

int	main(int argc, char **argv) {
	int	y;
	char	*raw;

	grid = (char **)malloc(sizeof(char *)*NLINES + (NLINES * WIDTH)+2);
	raw = (char *)(&grid[NLINES]);
	for(y=0; y<NLINES; y++)
		grid[y] = &raw[y*WIDTH];
	for(y=0; y<NLINES * WIDTH; y++)
		raw[y] = ' ';
	raw[NLINES*WIDTH  ] = '\n';
	raw[NLINES*WIDTH+1] = '\0';

	clear();
	while(1) {
		_zip->z_tma = 50000000 * 4;
		update();
		redrawwin();

		while(0 != _zip->z_tma)
			;
	}

	return 0;
}
