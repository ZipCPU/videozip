////////////////////////////////////////////////////////////////////////////////
//
// Filename:	sim/automaster_tb.cpp
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	This file calls and accesses the main.v function via the
//		MAIN_TB class found in main_tb.cpp.  When put together with
//	the other components here, this file will simulate (all of) the
//	host's interaction with the FPGA circuit board.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2015-2024, Gisselquist Technology, LLC
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
#include <signal.h>
#include <time.h>
#include <ctype.h>
#include <string.h>
#include <stdint.h>

#include "verilated.h"
#include "design.h"

#include "testb.h"
// #include "twoc.h"

#include "port.h"
// }}}

bool	gbl_use_gui = false, gbl_force_trace = false;

#include "main_tb.cpp"

void	usage(void) {
	// {{{
	fprintf(stderr, "USAGE: main_tb <options> [zipcpu-elf-file]\n");
	fprintf(stderr,
#ifdef	SDSPI_ACCESS
"\t-c <img-file>\n"
"\t\tSpecifies a memory image which will be used to make the SD-card\n"
"\t\tmore realistic.  Reads from the SD-card will be directed to\n"
"\t\t\"sectors\" within this image.\n\n"
#endif
"\t-g\tEnables the GUI, for video simulation\n"
"\t-l <time>\tLimits simulation time to the given time\n"
"\t-d\tSets the debugging flag so that the design may produce a trace.\n"
"\t\tWith only one '-d' argument, debugging will be enabled by the\n"
"\t\tmanagement CPU within the design.  With two '-d' arguments,\n"
"\t\ta trace will be produced indepenent of the CPU's control.\n"
"\t-t <filename>\n"
"\t\tEnables debugging and turns on tracing.  Traces will be written\n"
"\t\tto <filename>.  <filename> is assumed to be a vcd file name\n"
);
}
// }}}

void	cpu_sim_write(MAINTB *tb, unsigned addr, unsigned data) {
	// {{{
	tb->m_core->cpu_sim_cyc   = 1;
	tb->m_core->cpu_sim_stb   = 1;
	tb->m_core->cpu_sim_we    = 1;
	tb->m_core->cpu_sim_addr  = addr;
	tb->m_core->cpu_sim_data  = data;

	do {
		tb->tick_clk();
	} while(tb->m_core->cpu_sim_stall);

	tb->m_core->cpu_sim_stb   = 0;

	while(!tb->m_core->cpu_sim_ack)
		tb->tick_clk();

	tb->m_core->cpu_sim_cyc   = 0;
}
// }}}

int	main(int argc, char **argv) {
	// Variable declaration and initialization
	// {{{
#if	defined(VIDPIPE_ACCESS)
	// || defined(OLED_ACCESS)
	Gtk::Main	main_instance(argc, argv);
#endif
	Verilated::commandArgs(argc, argv);

	const	char *elfload = NULL,
#ifdef	SDSPI_ACCESS
			*sdimage_file = NULL,
#endif
			*profile_file = NULL,
			*trace_file = NULL; // "trace.vcd";
	bool	debug_flag = false,
		verbose_flag = false;
	FILE	*profile_fp;
	uint64_t	limit_time_ns = 0l,
		__attribute__((unused)) limit_time_ps = 0l;

	MAINTB	*tb;
	// }}}

	// Process arguments
	// {{{
	for(int argn=1; argn < argc; argn++) {
		if (argv[argn][0] == '-') for(int j=1;
					(j<512)&&(argv[argn][j]);j++) {
			switch(tolower(argv[argn][j])) {
#ifdef	SDSPI_ACCESS
			case 'c': sdimage_file = argv[++argn]; j = 1000; break;
#endif
			case 'd': gbl_force_trace = debug_flag; debug_flag = true;
				if (trace_file == NULL)
					trace_file = "trace.vcd";
				break;
			case 'g': gbl_use_gui = true; break;
			case 'l':
				limit_time_ns = strtoul(argv[++argn], NULL, 0);
				limit_time_ps = limit_time_ns * 1000;
				j = 1000;
				break;
			case 'f': profile_file = "pfile.bin"; break;
			case 't': gbl_force_trace = debug_flag; debug_flag = true;
				trace_file = argv[++argn]; j=1000; break;
			case 'h': usage(); exit(0); break;
			case 'v': verbose_flag = true; break;
			default:
				fprintf(stderr, "ERR: Unexpected flag, -%c\n\n",
					argv[argn][j]);
				usage();
				break;
			}
		} else if (iself(argv[argn])) {
			elfload = argv[argn];
#ifdef	SDSPI_ACCESS
		} else if (0 == access(argv[argn], R_OK)) {
			sdimage_file = argv[argn];
#endif
		} else {
			fprintf(stderr, "ERR: Cannot read %s\n", argv[argn]);
			perror("O/S Err:");
			exit(EXIT_FAILURE);
		}
	}
	// }}}

	// Setup
	// {{{
	tb = new MAINTB;

	if (debug_flag && verbose_flag) {
		printf("Opening design with\n");
		printf("\tDebug Access port = %d\n", FPGAPORT); // fpga_port);
		printf("\tSerial Console    = %d\n", FPGAPORT+1);
		printf("\tVCD File         = %s\n", trace_file);
		if (elfload)
			printf("\tELF File         = %s\n", elfload);
	} if (trace_file)
		tb->opentrace(trace_file);

	if (profile_file) {
#ifndef	INCLUDE_ZIPCPU
		fprintf(stderr, "ERR: Design has no ZipCPU\n");
		exit(EXIT_FAILURE);
#endif
		profile_fp = fopen(profile_file, "w");
		if (profile_fp == NULL) {
			fprintf(stderr, "ERR: Cannot open profile output "
				"file, %s\n", profile_file);
			exit(EXIT_FAILURE);
		}
	} else
		profile_fp = NULL;
	// }}}

	tb->m_core->i_net_rx_dv  =  0;
	tb->m_core->i_net_rx_err =  0;
	tb->m_core->i_net_rxd    = 13;
#ifndef	INCLUDE_ZIPCPU
	tb->m_core->cpu_sim_cyc  = 0;
	tb->m_core->cpu_sim_stb  = 0;
	tb->m_core->cpu_sim_we   = 0;
	tb->m_core->cpu_sim_addr = 0;
	tb->m_core->cpu_sim_data = 0;
	tb->m_core->cpu_sim_sel  = 0;
#endif
	tb->reset();
#ifdef	SDSPI_ACCESS
	tb->setsdcard(sdimage_file);
#endif

	// Load the ZipCPU
	// {{{
	if (elfload) {
#ifndef	INCLUDE_ZIPCPU
		fprintf(stderr, "ERR: Design has no ZipCPU\n");
		exit(EXIT_FAILURE);
#endif
		tb->loadelf(elfload);

		ELFSECTION	**secpp;
		uint32_t	entry;

		elfread(elfload, entry, secpp);
		free(secpp);

		if (verbose_flag)
			printf("Attempting to start ZipCPU from 0x%08x\n", entry);

		// Halt the CPU
		// {{{
		cpu_sim_write(tb, 0x0, 0x001);	// Set the halt bit
		// }}}

		// Clear all registers
		// {{{
		for(int k=0; k<32; k++)
			cpu_sim_write(tb, k+32, 0x00);
		// }}}

		// Write the IPC register
		// {{{
		cpu_sim_write(tb, 15+32, entry);
		// }}}

		// Clear the cache
		// {{{
		cpu_sim_write(tb, 0, 0x31);
		// }}}

		// Start the CPU, clear the halt bit
		// {{{
		cpu_sim_write(tb, 0, 0x20);
		// }}}
	}
	// }}}

	// Main while(1) loop
	// {{{
#if	defined(VIDPIPE_ACCESS)
	//  || defined(OLED_ACCESS)
	if (gbl_use_gui) {
		printf("CONNECT\n");

		tb->connect_idler();
		Gtk::Main::run(*tb->m_hdmitx);
	} else
#endif
	if (profile_fp) { // Profile the ZipCPU
		// {{{
		unsigned last_instruction_tick = 0;
		while(!tb->done() && (limit_time_ps == 0
					|| tb->m_time_ps <= limit_time_ps)) {
			unsigned long	iticks;
			unsigned	buf[2];

			tb->tick_clk();

			if (tb->m_core->cpu_prof_stb) {
				unsigned	now;

				now = tb->m_core->cpu_prof_ticks;
				iticks = now - last_instruction_tick;
				buf[0] = tb->m_core->cpu_prof_addr;
				buf[1] = (unsigned)iticks;
				fwrite(buf, sizeof(unsigned), 2, profile_fp);

				last_instruction_tick = now;
			}
		}
		// }}}
	} else if (limit_time_ps > 0l) {
		while(!tb->done() && tb->m_time_ps <= limit_time_ps) {
			tb->tick();
			tb->pausetrace(!gbl_force_trace && !tb->m_core->o_trace);
		}
	} else while(!tb->done()) {
		tb->tick();
		tb->pausetrace(!gbl_force_trace && !tb->m_core->o_trace);
	}
	// }}}

	tb->close();
	delete tb;

	return	EXIT_SUCCESS;
}
