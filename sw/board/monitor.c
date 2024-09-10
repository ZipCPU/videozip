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

__attribute__((noinline))
void	mvprintw(int y, int x, char *fmt, ...) {
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

void	redrawwin(void) {
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

void	clear(void) {
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

void	clkout(int y, int x, char *str, unsigned v) {
	double hz = v;

	if (hz < 1e3)
		mvprintw(y, x, "%12s:       %3.0f Hz", str, hz);
	else if (hz < 1e6)
		mvprintw(y, x, "%12s:    %7.3f kHz", str, hz / 1000.0);
	else
		mvprintw(y, x, "%12s: %8.2f MHz", str, hz / 1e6);
}

void	update(void) {
	mvprintw(0, 0, "Version: %08x", *_version);
	mvprintw(0,20, "BuildTime: %06x", *_buildtime & 0x0ffffff);
#ifdef	_BOARD_HAS_SPIO
	{
		unsigned spiov = *_spio;

		// Buttons
		mvaddstr(1, 8, (spiov & 0x010000) ? "1":"0");
		mvaddstr(2,10, (spiov & 0x020000) ? "1":"0");
		mvaddstr(2, 6, (spiov & 0x040000) ? "1":"0");
		mvaddstr(3, 8, (spiov & 0x080000) ? "1":"0");
		mvaddstr(2, 8, (spiov & 0x100000) ? "1":"0");

		// Switches
		mvaddstr(5, 0, (spiov & 0x08000) ? "1":"0");
		mvaddstr(5, 2, (spiov & 0x04000) ? "1":"0");
		mvaddstr(5, 4, (spiov & 0x02000) ? "1":"0");
		mvaddstr(5, 6, (spiov & 0x01000) ? "1":"0");
		//
		mvaddstr(5,10, (spiov & 0x00800) ? "1":"0");
		mvaddstr(5,12, (spiov & 0x00400) ? "1":"0");
		mvaddstr(5,14, (spiov & 0x00200) ? "1":"0");
		mvaddstr(5,16, (spiov & 0x00100) ? "1":"0");
	}
#endif
#ifdef	_BOARD_HAS_GPIO
	{
		unsigned gpiov = *_gpio;
		mvaddstr(7, 0, "Outputs:");
		mvaddstr(7,40, "Inputs:");
		mvaddstr(8, 0, "------------------------------");
		mvaddstr(8,40, "------------------------------");

		// mvprintw( 9, 1, "%-20s", (gpiov & 0x01) ? "HDMI-RX CEC":"");
		// mvprintw(10, 1, "%-20s", (gpiov & 0x02) ? "HDMI-TX CEC":"");
		mvprintw( 9, 1, "%-20s", (gpiov & 0x04) ? "HDMI TX EN":"");
		mvprintw(10, 1, "%-20s", (gpiov & 0x08) ? "HDMI RX HPA":"");
		// mvprintw(11, 1, "%-20s", (gpiov & 0x10) ? "":"SD-RESET");
		mvprintw(12, 1, "%-20s", (gpiov & 0x20) ? "OLED-RESET":"");
		mvprintw(13, 1, "%-20s", (gpiov & 0x40) ? "OLED PANEL EN":"");
		mvprintw(14, 1, "%-20s", (gpiov & 0x80) ? "OLED LOGIC EN":"");

		// mvprintw( 9,41,"%-20s",(gpiov & 0x010000)? "HDMI-RX CEC":"");
		// mvprintw(10,41,"%-20s",(gpiov & 0x020000)? "HDMI-TX CEC":"");
		// mvprintw(11,41, "%-20s", (gpiov & 0x040000) ? "HDMI TX EN":"");
		// mvprintw(14,41, "%-20s", (gpiov & 0x200000) ? "GPS 3DF":"");
		mvprintw( 9,41,"%-20s", (gpiov & 0x080000) ? "SD Card detect":"");
		mvprintw(10,41,"%-20s", (gpiov & 0x100000) ? "HDMI-TX Hotplug det":"");
		mvprintw(11,41,"%-20s", (gpiov & 0x400000) ? "SYSCLK Locked":"");
		mvprintw(12,41,"%-20s", (gpiov & 0x800000) ? "PXRX Clk locked":"");
	}
#endif

	mvaddstr(16, 0, "Clocks:");
	mvaddstr(17, 0, "------------------------------");
	clkout(18,1, "Network RX", *_netclockctr);
	clkout(19,1, "Network TX", *_nettxctr);
	clkout(20,1, "HDMI RX", _hdmi->v_hdmifreq);
	clkout(21,1, "HDMI TX", _hdmi->v_pxfreq);

#ifdef	_BOARD_HAS_MEGANET
	mvaddstr(16, 40, "Network:");
	mvaddstr(17,40, "------------------------------");
	mvprintw(18, 41, "%13s %7d/%7d", "Packets:", _net->n_rxpkt & 0x0fffffff, _net->n_txpkt);
	mvprintw(19, 41, "%13s %7d/%7d", "ARP Packets:",  _net->n_rxarp, _net->n_txarp);
	mvprintw(20, 41, "%13s %7d/%7d", "ICMP Packets:", _net->n_rxicmp, _net->n_txicmp);
	// mvaddstr(21, 41, "%13s %7d/%7d", "CPU Packets:",  0, 0);
#endif

#ifdef	_BOARD_HAS_VIDPIPE
	{
		unsigned	vpipe;

		vpipe = _hdmi->v_control;
		mvaddstr(0, 40, "HDMI:");
		mvaddstr(1, 40, "------------------------------");

		if (vpipe & 1) {
			mvprintw(0, 50, "%-30s","Reset");
			mvprintw(2, 41, "%-20s","Size:");
			mvprintw(3, 41, "%-20s","Porch:");
			mvprintw(4, 41, "%-20s","Sync:");
			mvprintw(5, 41, "%-20s","Raw:");
			mvprintw(2, 61, "%-20s","FPS:");
			mvprintw(3, 61, "%-20s","Sync:");
		} else {
			if (0 == (vpipe & 0x020))
				mvaddstr(0, 60, "CLK: Lcl");
			else if (0x20 == (vpipe & 0x020))
				mvaddstr(0, 60, "CLK: RX");

			if (0 == (vpipe & 0x040))
				mvaddstr(0, 70, "[Local]");
			else // if (0x40 == (vpipe & 0x040))
				mvaddstr(0, 70, "External");

			mvprintw(2, 41, "Size:  %4d x %4d",	// 18ch
				_hdmi->v_in.m_height, _hdmi->v_in.m_width);
			mvprintw(3, 41, "Porch: %4d x %4d",
				_hdmi->v_in.m_vporch, _hdmi->v_in.m_hporch);
			mvprintw(4, 41, "Sync:  %4d x %4d",
				_hdmi->v_in.m_vsync, _hdmi->v_in.m_hsync);
			mvprintw(5, 41, "Raw:   %4d x %4d",
				_hdmi->v_in.m_raw_height, _hdmi->v_in.m_raw_width);

			mvprintw(2, 60, "FPS:  0x%08x", _hdmi->v_fps);
			mvprintw(3, 60, "SYNC: 0x%08x %s", _hdmi->v_syncword,
				(_hdmi->v_syncword & 0x1000000) ? "Locked":"(No sync)");
		}
	}
#endif
}

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
