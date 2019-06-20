////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./testb.h
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// DO NOT EDIT THIS FILE!
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga autofpga -d -o . allclocks.txt genclk.txt netclockctr.txt global.txt dlyarbiter.txt icape.txt version.txt buserr.txt pic.txt pwrcount.txt xpander.txt vidarbiter.txt spio.txt gpio.txt rtcgps.txt rtcdate.txt wbuconsole.txt bkram.txt flash.txt sdvidram.txt zipmaster.txt mdio.txt enet.txt gps.txt sdspi.txt hdmi.txt cpuscope.txt enetscope.txt flashscope.txt mdioscope.txt mem_bkram_only.txt mem_flash_bkram.txt clkcounter.txt wbmouse.txt wbpmic.txt xdc.txt
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
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
#ifndef	TESTB_H
#define	TESTB_H

#include <stdio.h>
#include <stdint.h>
#include <verilated_vcd_c.h>
#include <tbclock.h>

template <class VA>	class TESTB {
public:
	VA	*m_core;
	bool		m_changed;
	VerilatedVcdC*	m_trace;
	bool		m_done;
	uint64_t	m_time_ps;
	// TBCLOCK is a clock support class, enabling multiclock simulation
	// operation.
	TBCLOCK	m_clk;
	TBCLOCK	m_net_rx_clk;
	TBCLOCK	m_hdmi_out_clk;
	TBCLOCK	m_hdmi_in_clk;
	TBCLOCK	m_hdmi_in_hsclk;
	TBCLOCK	m_clk_200mhz;
	TBCLOCK	m_clk_125mhz;

	TESTB(void) {
		m_core = new VA;
		m_time_ps  = 0ul;
		m_trace    = NULL;
		m_done     = false;
		Verilated::traceEverOn(true);
// Set the initial clock periods
		m_clk.init(10000);	//  100.00 MHz
		m_net_rx_clk.init(8000);	//  125.00 MHz
		m_hdmi_out_clk.init(6734);	//  148.50 MHz
		m_hdmi_in_clk.init(6734);	//  148.50 MHz
		m_hdmi_in_hsclk.init(673);	// 1485.88 MHz
		m_clk_200mhz.init(5000);	//  200.00 MHz
		m_clk_125mhz.init(8000);	//  125.00 MHz
	}
	virtual ~TESTB(void) {
		if (m_trace) m_trace->close();
		delete m_core;
		m_core = NULL;
	}

	virtual	void	opentrace(const char *vcdname) {
		if (!m_trace) {
			m_trace = new VerilatedVcdC;
			m_core->trace(m_trace, 99);
			m_trace->spTrace()->set_time_resolution("ps");
			m_trace->spTrace()->set_time_unit("ps");
			m_trace->open(vcdname);
		}
	}

	void	trace(const char *vcdname) {
		opentrace(vcdname);
	}

	virtual	void	closetrace(void) {
		if (m_trace) {
			m_trace->close();
			delete m_trace;
			m_trace = NULL;
		}
	}

	virtual	void	eval(void) {
		m_core->eval();
	}

	virtual	void	tick(void) {
		unsigned	mintime = m_clk.time_to_edge();

		if (m_net_rx_clk.time_to_edge() < mintime)
			mintime = m_net_rx_clk.time_to_edge();

		if (m_hdmi_out_clk.time_to_edge() < mintime)
			mintime = m_hdmi_out_clk.time_to_edge();

		if (m_hdmi_in_clk.time_to_edge() < mintime)
			mintime = m_hdmi_in_clk.time_to_edge();

		if (m_hdmi_in_hsclk.time_to_edge() < mintime)
			mintime = m_hdmi_in_hsclk.time_to_edge();

		if (m_clk_200mhz.time_to_edge() < mintime)
			mintime = m_clk_200mhz.time_to_edge();

		if (m_clk_125mhz.time_to_edge() < mintime)
			mintime = m_clk_125mhz.time_to_edge();

		assert(mintime > 1);

		// Pre-evaluate, to give verilator a chance to settle any
		// combinatorial logic thatthat may have changed since the
		// last clockevaluation, and then record that in the trace.
		eval();
		if (m_trace) m_trace->dump(m_time_ps+1);

		// Advance each clock
		m_core->i_clk = m_clk.advance(mintime);
		m_core->i_net_rx_clk = m_net_rx_clk.advance(mintime);
		m_core->i_hdmi_out_clk = m_hdmi_out_clk.advance(mintime);
		m_core->i_hdmi_in_clk = m_hdmi_in_clk.advance(mintime);
		m_core->i_hdmi_in_hsclk = m_hdmi_in_hsclk.advance(mintime);
		m_core->i_clk_200mhz = m_clk_200mhz.advance(mintime);
		m_core->i_clk_125mhz = m_clk_125mhz.advance(mintime);

		m_time_ps += mintime;
		eval();
		// If we are keeping a trace, dump the current state to that
		// trace now
		if (m_trace) {
			m_trace->dump(m_time_ps);
			m_trace->flush();
		}

		if (m_clk.falling_edge()) {
			m_changed = true;
			sim_clk_tick();
		}
		if (m_net_rx_clk.falling_edge()) {
			m_changed = true;
			sim_net_rx_clk_tick();
		}
		if (m_hdmi_out_clk.falling_edge()) {
			m_changed = true;
			sim_hdmi_out_clk_tick();
		}
		if (m_hdmi_in_clk.falling_edge()) {
			m_changed = true;
			sim_hdmi_in_clk_tick();
		}
		if (m_hdmi_in_hsclk.falling_edge()) {
			m_changed = true;
			sim_hdmi_in_hsclk_tick();
		}
		if (m_clk_200mhz.falling_edge()) {
			m_changed = true;
			sim_clk_200mhz_tick();
		}
		if (m_clk_125mhz.falling_edge()) {
			m_changed = true;
			sim_clk_125mhz_tick();
		}
	}

	virtual	void	sim_clk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_net_rx_clk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_hdmi_out_clk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_hdmi_in_clk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_hdmi_in_hsclk_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_clk_200mhz_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual	void	sim_clk_125mhz_tick(void) {
		// AutoFPGA will override this method within main_tb.cpp if any
		// @SIM.TICK key is present within a design component also
		// containing a @SIM.CLOCK key identifying this clock.  That
		// component must also set m_changed to true.
		m_changed = false;
	}
	virtual bool	done(void) {
		if (m_done)
			return true;

		if (Verilated::gotFinish())
			m_done = true;

		return m_done;
	}

	virtual	void	reset(void) {
		m_core->i_reset = 1;
		tick();
		m_core->i_reset = 0;
		// printf("RESET\n");
	}
};

#endif	// TESTB

