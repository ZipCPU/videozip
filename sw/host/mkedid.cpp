////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	mkedid.cpp
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	To create a memory set, describing the EDID information of an
//		HDMI input port, that can then be read via readmemh.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017, Gisselquist Technology, LLC
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
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#include "regdefs.h"

#define	MFID(A,B,C)	(	(((toupper(A)-'A'+1)&0x01f)<<10)| \
				(((toupper(B)-'A'+1)&0x01f)<< 5)| \
				 ((toupper(C)-'A'+1)&0x01f))

typedef	enum {
	ASPECT_16_10= 0,
	ASPECT_4_3  = 1,
	ASPECT_5_4  = 2,
	ASPECT_16_9 = 3
} ASPECT_ENUM;;

void	set_standard_timing(unsigned char *edata, const int hpixels,
		const ASPECT_ENUM ar, int refresh_rate) {
	int	r;
	r = ((hpixels/8-31) & 0x0ff) << 8;
	r |= (((int)ar)&3)<<6;
	r |= (refresh_rate-60)&0x03f;

	edata[0] = ((r>>8)&0x0ff);
	edata[1] = (r & 0x0ff);
}

#define	SID_SERIALNUM	0x0ff
#define	SID_ASCIISTR	0x0fe
#define	SID_DSPNAME	0x0fc

void	monitor_string(unsigned char *edata, int sid, const char *str) {
	const char *ptr = str;
	int	ei = 0, hln;

	edata[ei++] = 0x00;
	edata[ei++] = 0x00;
	edata[ei++] = 0x00;
	edata[ei++] = sid;
	edata[ei++] = 0x00;
	hln = ei;
	while((*ptr)&&(ei < 13+hln))
		edata[ei++] = *ptr++;
	edata[ei++] = '\n';
	while(ei < 13+hln-1)
		edata[ei++] = ' ';
}


unsigned char checksum(const unsigned char *edid) {
	int	sum=0;
	for(int i=0; i<127; i++)
		sum += edid[i] & 0x0ff;
	return (256-sum)&0x0ff;
}

/*
* usage()
*
* Tell the user the calling conventions of this program, and what the program
* can be used to accomplish.
*/
void	usage(void) {
	fprintf(stderr, "USAGE:\tmkedid [-o <outfile>]\n");
	fprintf(stderr, "\n"
"\tCreates an EDID information field, such as might be used to identify\n"
"\tdisplay resolutions an HDMI converter might support, and writes the\n"
"\tresult to a hexfile.\n"
"\n\n");
}

static	const	int	NEDID = 128;
int main(int argc, char **argv) {
	FILE	*fout;
	const	char	*output_filename = NULL;
	unsigned char	edid[NEDID];
	unsigned serial_num = 0;	// 32-bit serial number
	time_t	mftime;
	struct	tm *tmp;

	for(int argn=1; argn < argc; argn++) {
		if (argv[argn][0] == '-') {
			if (argv[argn][2] == '\0') {
				if (argv[argn][1] == 'o') {
					if (argn+1<argc)
						output_filename = argv[++argn];
					else  {
					fprintf(stderr, "ERR: -o given, but no filename given");
						usage();
						exit(EXIT_FAILURE);
					}
				} else {
					fprintf(stderr, "ERR: Unknown argument, %s\n", argv[argn]);
					usage();
					exit(EXIT_FAILURE);
				}
			} else {
				fprintf(stderr, "ERR: Unknown argument, %s\n", argv[argn]);
				usage();
				exit(EXIT_FAILURE);
			}
		} else {
			fprintf(stderr, "ERR: Unknown parameter, %s\n", argv[argn]);
			usage();
			exit(EXIT_FAILURE);
		}
	}

	if (output_filename == NULL)
		output_filename = "edid.hex";

	// fout = fopen(output_filename, "w");
	// if (fout == NULL) {
		// fprintf(stderr, "Err: Cannot write %s\n", output_filename);
		// exit(EXIT_FAILURE);
	// }

	// Build the EDID memory

	// First the header
	edid[0] = 0;
	for(unsigned i=1; i<7; i++)
		edid[i] = 0x0ff;
	edid[7] = 0;

	// Then any vendor or product information
	// edid[8...11]
	edid[0x08] = 0x10;	// DELL EISA ID
	edid[0x09] = 0xac;	// Compressed ASCII
	edid[0x08] = (MFID('G','Q','T')>>8);
	edid[0x09] = (MFID('G','Q','T')&0x0ff);
	edid[0x0a] = 0xdd;	// Product code
	edid[0x0b] = 0xda;
	edid[0x0c] = 0x00;	// 32-bit serial #
	edid[0x0d] = 0x00;
	edid[0x0e] = 0x00;
	edid[0x0f] = 0x00;
	edid[0x0c] =  serial_num      & 0x0ff;
	edid[0x0d] = (serial_num>> 8) & 0x0ff;
	edid[0x0e] = (serial_num>>16) & 0x0ff;
	edid[0x0f] = (serial_num>>24) & 0x0ff;

	mftime = time(NULL);
	tmp = localtime(&mftime);	// tmp = time pointer ...
	edid[0x10] = ((tmp->tm_yday-1)/7)+1;	// Week of manufacture
	edid[0x11] = tmp->tm_year-90;		// Year of manufacture

	edid[0x12] = 0x01;	// EDID structure version
	edid[0x13] = 0x03;	// EDID revision ID

	edid[0x14] = 0x0e;	// Video input definition
			// 1'b0 Analog input
			// 2'b00 0.3-0.7 Vpp
			// 1'b0 NO blank-to-black setup
			// 1'b1 Separate syncs supported
			// 1'b1 Composite sync supported
			// 1'b1 Sync on green video supported
			// 1'b0 No serration on VSync pulse is required
	edid[0x15] = 0x26;	// Max H image size (38 cm)
	edid[0x16] = 0x1d;	// Max V image size (29 cm)
	edid[0x17] = 0x0e;	// Display Gamma (Gamma 2.5)
	edid[0x18] = 0xef;	// Feature support:
			// 1'b1 standby,
			// 1'b1 suspend,
			// 1'b1 active off,
			// 2'b10 rgb color (vice monochrome/grayscale, R/G/Y or undef),
			// 1'b1 sRGB,
			// 1'b1 preferred timing in first detailed timing block,
			// 1'b1 default GTF
	edid[0x19] = 0xee;	// Red/green low bits
	edid[0x1a] = 0x91;	// Blue/white low bits
	edid[0x1b] = 0xa3;	// Red x / high bits
	edid[0x1c] = 0x54;	// Red y
	edid[0x1d] = 0x4c;	// Green x
	edid[0x1e] = 0x99;	// Green y
	edid[0x1f] = 0x26;	// Blue x
	edid[0x20] = 0x0f;	// Blue y
	edid[0x21] = 0x50;	// White x
	edid[0x22] = 0x54;	// White y
	edid[0x23] = 0xa5;	// Established timing I
			// 1'b1: 720x400@70,
			// 1'b0: 720x400@88
			// 1'b1: 640x480@60
			// 1'b0: 640x480@67
			// 1'b0: 640x480@72
			// 1'b1: 640x480@75
			// 1'b0: 800x600@56
			// 1'b1: 800x600@60
	edid[0x24] = 0x43;	// Established timing II(800x600@75,1024x768@75,1280x1024@75)
			// 1'b0:  800x 600@72
			// 1'b1:  800x 600@75
			// 1'b0:  832x 624@75
			// 1'b0: 1024x 768@87
			// 1'b0: 1024x 768@60
			// 1'b0: 1024x 768@70
			// 1'b1: 1024x 768@75
			// 1'b1: 1280x1024@75

	edid[0x25] = 0x00;	// Established timing III (none)
	// Standard timings #1-8
	set_standard_timing(&edid[0x26], 1600, ASPECT_4_3, 75); // 1600x1200@75
	set_standard_timing(&edid[0x28], 1600, ASPECT_4_3, 85); // 1600x1200@85
	set_standard_timing(&edid[0x2a], 1152, ASPECT_4_3, 85); // 1152x 864@85
	set_standard_timing(&edid[0x2c], 1024, ASPECT_4_3, 85); // 1024x 768@85
	set_standard_timing(&edid[0x2e],  800, ASPECT_4_3, 85); //  800x 600@85
	set_standard_timing(&edid[0x30],  640, ASPECT_4_3, 85); //  640x 480@85
	set_standard_timing(&edid[0x32], 1800, ASPECT_5_4, 75); // 1800x1440@75
	edid[0x34] = 0x01;	// Standard timing #8	-- NOT USED
	edid[0x35] = 0x01;
	edid[0x36] = 0x86;	// Detailed timing/monitor descriptor #1
	edid[0x37] = 0x3d;	// 1280x1024@85Hz, 157.5MHz
	edid[0x38] = 0x00;	// Hor active = 1280
	edid[0x39] = 0xc0;	// Hor blanking = 448
	edid[0x3a] = 0x51;	//
	edid[0x3b] = 0x00;	// Vertical active = 1024 linse
	edid[0x3c] = 0x30;	// Vertical blanking = 48 linse
	edid[0x3d] = 0x40;	//
	edid[0x3e] = 0x40;	// Hor sync offset =  64 pixels
	edid[0x3f] = 0xa0;	// Hor sync width  = 160 pixels
	edid[0x40] = 0x13;	// Ver sync offset =  1 line
	edid[0x41] = 0x00;	// Ver sync width  =  3 lines
	edid[0x42] = 0x7c;	// H image size = 380mm
	edid[0x43] = 0x22;	// V image size = 290mm
	edid[0x44] = 0x11;	//
	edid[0x45] = 0x00;	// No horizontal border
	edid[0x46] = 0x00;	// No vertical  border
	edid[0x47] = 0x1e;	// Separate digital syncs, H/V polarity
	edid[0x48] = 0x00;	// Detailed timing/monitor descriptor #2
	//
	edid[0x49] = 0x00;	// Monitor serial number
	edid[0x4a] = 0x00;	// 55347BONZH47
	edid[0x4b] = 0xff;	//
	edid[0x4c] = 0x00;	//
	edid[0x4d] = 0x35;	// 5
	edid[0x4e] = 0x35;	// 5
	edid[0x4f] = 0x33;	// 3
	edid[0x50] = 0x34;	// 4
	edid[0x51] = 0x37;	// 7
	edid[0x52] = 0x42;	//
	edid[0x53] = 0x4f;	// O
	edid[0x54] = 0x4e;	// N
	edid[0x55] = 0x5a;	// Z
	edid[0x56] = 0x48;	// H
	edid[0x57] = 0x34;	// 4
	edid[0x58] = 0x37;	// 7
	edid[0x59] = 0x0a;	// \n
	monitor_string(&edid[0x48], SID_SERIALNUM, "0xDaDD");
	edid[0x5a] = 0x00;	// Detailed timing/monitor descriptor #3
	edid[0x5b] = 0x00;
	edid[0x5c] = 0x00;	// Monitor name
	edid[0x5d] = 0xFC;	// DELL UR111
	edid[0x5e] = 0x00;	//
	edid[0x5f] = 0x44;	// D
	edid[0x60] = 0x45;	// E
	edid[0x61] = 0x4c;	// L
	edid[0x62] = 0x4c;	// L
	edid[0x63] = 0x20;	//
	edid[0x64] = 0x55;	// U
	edid[0x65] = 0x52;	// R
	edid[0x66] = 0x31;	// 1
	edid[0x67] = 0x31;	// 1
	edid[0x68] = 0x31;	// 1
	edid[0x69] = 0x0a;	// \n
	edid[0x6a] = 0x0a;	//
	monitor_string(&edid[0x5a], SID_DSPNAME, "VideoZip");
	edid[0x6b] = 0x0a;	//
	edid[0x6c] = 0x0a;	// Detailed timing/monitor descriptor #4
	edid[0x6d] = 0x0a;	// \n
	edid[0x6e] = 0x0a;	// MONITOR RANGE LIMITS
	edid[0x6f] = 0xfd;	//
	edid[0x70] = 0x00;	//
	edid[0x71] = 0x30;	// Vertical range (48Hz)
	edid[0x72] = 0xa0;	//	(160Hz)
	edid[0x73] = 0x1e;	// Horizontal range (30kHz)
	edid[0x74] = 0x79;	//	(121kHz)
	edid[0x75] = 0x1c;	// Max dot clock (280MHz)
	edid[0x76] = 0x02;	// Secondary GTF
	edid[0x77] = 0x00;	// Reserved 00
	edid[0x78] = 0x28;	// Start freq 80kHz
	edid[0x79] = 0x50;	// C=40
	edid[0x7a] = 0x10;	// M=3600
	edid[0x7b] = 0x0e;	//
	edid[0x7c] = 0x80;	// K=128
	edid[0x7d] = 0x46;	// J=35
	edid[0x7e] = 0x00;	// Extension flag
	edid[0x7f] = checksum(edid);	// Checksum

	if (1) {
		// Bulid a proper hex file
		int	linelen = 0;
		int	ch, addr = 0;
		char	fnbuf[16];

		for(int a=0; a<4; a++) {
			addr = a;
			linelen = 0;

			sprintf(fnbuf, "edid-%c.hex", a+'a');
			fout = fopen(fnbuf, "w");
			fprintf(fout, "@%08x ", addr-a); linelen += 4+6;
			for(int i=a; i<NEDID; i+=4) {
				ch = edid[i];
				fprintf(fout, "%02x ", ch & 0x0ff); linelen += 3; addr++;

				if (linelen >= 77) {
					fprintf(fout, "\n");
					linelen = 0;
					fprintf(fout, "@%08x ", addr-a);
					linelen += 4+6;
				}
			} fprintf(fout, "\n");
			fclose(fout);
		}
	}

	if(1) {
		fout = fopen("edid.sh", "w");
		fprintf(fout, "#!/bin/bash\n##\nWBREGS=./wbregs\n\n");

		for(int i=0; i<32; i++) {
			unsigned val, base = (i<<2);

			val = edid[base];
			val = (val << 8) | edid[base+1];
			val = (val << 8) | edid[base+2];
			val = (val << 8) | edid[base+3];

			fprintf(fout, "$WBREGS 0x%x 0x%08x #%c%c%c%c\n",
				base+R_EDID_IN, val,
				((isprint(edid[base  ]))?edid[base  ]:'.'),
				((isprint(edid[base+1]))?edid[base+1]:'.'),
				((isprint(edid[base+2]))?edid[base+2]:'.'),
				((isprint(edid[base+3]))?edid[base+3]:'.'));
		}
	}
}
