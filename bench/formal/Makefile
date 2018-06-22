################################################################################
##
## Filename:	Makefile
##
## Project:	Zip CPU -- a small, lightweight, RISC CPU soft core
##
## Purpose:	To direct the formal verification of particular components of
##		the ZipCPU.
##
## Targets:	The default target, all, tests all of the components within
##		this module.
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017-2018, Gisselquist Technology, LLC
##
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of  the GNU General Public License as published
## by the Free Software Foundation, either version 3 of the License, or (at
## your option) any later version.
##
## This program is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
## for more details.
##
## You should have received a copy of the GNU General Public License along
## with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
## target there if the PDF file isn't present.)  If not, see
## <http://www.gnu.org/licenses/> for a copy.
##
## License:	GPL, v3, as defined and found on www.gnu.org,
##		http://www.gnu.org/licenses/gpl.html
##
##
################################################################################
##
##
TESTS := addecrc addemac addepad addepreambl
TESTS += rxecrc rxehwmac rxeipchk rxemin rxepreambl rxewrite
.PHONY: $(TESTS)
all: $(TESTS)
RTL    := ../../rtl
NETRTL := $(RTL)/ethernet

SMTBMC  := yosys-smtbmc
# SOLVER  := -s z3
SOLVER  := -s yices
# SOLVER  := -s boolector
BMCARGS := --presat $(SOLVER)
INDARGS := $(SOLVER) -i

TXCRC  := addecrc
TXMAC  := addemac
TXPAD  := addepad
TXPRE  := addepreamble
RXCRC  := rxecrc
RXMAC  := rxehwmac
RXPAD  := rxemin
RXPRE  := rxepreambl
RXIPK  := rxeipchk
RXWRT  := rxewrite

$(TXCRC).smt2: $(NETRTL)/$(TXCRC).v $(TXCRC).ys
	yosys -ql $(TXCRC).yslog -s $(TXCRC).ys

$(TXMAC).smt2: $(NETRTL)/$(TXMAC).v $(TXMAC).ys
	yosys -ql $(TXMAC).yslog -s $(TXMAC).ys

$(TXPAD).smt2: $(NETRTL)/$(TXPAD).v $(TXPAD).ys
	yosys -ql $(TXPAD).yslog -s $(TXPAD).ys

$(TXPRE).smt2: $(NETRTL)/$(TXPRE).v $(TXPRE).ys
	yosys -ql $(TXPRE).yslog -s $(TXPRE).ys

$(RXCRC).smt2: $(NETRTL)/$(RXCRC).v $(RXCRC).ys
	yosys -ql $(RXCRC).yslog -s $(RXCRC).ys

$(RXMAC).smt2: $(NETRTL)/$(RXMAC).v $(RXMAC).ys
	yosys -ql $(RXMAC).yslog -s $(RXMAC).ys

$(RXPRE).smt2: $(NETRTL)/$(RXPRE).v $(RXPRE).ys
	yosys -ql $(RXPRE).yslog -s $(RXPRE).ys

$(RXPAD).smt2: $(NETRTL)/$(RXPAD).v $(RXPAD).ys
	yosys -ql $(RXPAD).yslog -s $(RXPAD).ys

$(RXIPK).smt2: $(NETRTL)/$(RXIPK).v $(RXIPK).ys
	yosys -ql $(RXIPK).yslog -s $(RXIPK).ys

$(RXWRT).smt2: $(NETRTL)/$(RXWRT).v $(RXWRT).ys
	yosys -ql $(RXWRT).yslog -s $(RXWRT).ys


$(TXCRC) : $(TXCRC).check
$(TXCRC).check: $(TXCRC).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 60 --dump-vcd $(TXCRC).vcd $(TXCRC).smt2
	$(SMTBMC) -g $(BMCARGS) -t 60 --dump-vcd $(TXCRC).vcd $(TXCRC).smt2
	$(SMTBMC)    $(INDARGS) -t 58 --dump-vcd $(TXCRC).vcd $(TXCRC).smt2
	touch $@


$(TXPAD) : $(TXPAD).check
$(TXPAD).check: $(TXPAD).smt2
	@rm -f $@
	$(SMTBMC) $(BMCARGS) -t 80 --dump-vcd $(TXPAD).vcd $(TXPAD).smt2
	$(SMTBMC) $(INDARGS) -t 58 --dump-vcd $(TXPAD).vcd $(TXPAD).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(TXPAD).vcd $(TXPAD).smt2
	touch $@

$(TXPRE) : $(TXPRE).check
$(TXPRE).check: $(TXPRE).smt2
	@rm -f $@
	$(SMTBMC) $(BMCARGS) -t 80 --dump-vcd $(TXPRE).vcd $(TXPRE).smt2
	$(SMTBMC) $(INDARGS) -t 76 --dump-vcd $(TXPRE).vcd $(TXPRE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 80 --dump-vcd $(TXPRE).vcd $(TXPRE).smt2
	touch $@


$(TXMAC) : $(TXMAC).check
$(TXMAC).check: $(TXMAC).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 48 --dump-vcd $(TXMAC).vcd $(TXMAC).smt2
	$(SMTBMC)    $(INDARGS) -t 48 --dump-vcd $(TXMAC).vcd $(TXMAC).smt2
	$(SMTBMC) -g $(BMCARGS) -t 46 --dump-vcd $(TXMAC).vcd $(TXMAC).smt2
	touch $@

$(RXCRC) : $(RXCRC).check
$(RXCRC).check: $(RXCRC).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(RXCRC).vcd $(RXCRC).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(RXCRC).vcd $(RXCRC).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(RXCRC).vcd $(RXCRC).smt2
	touch $@

$(RXMAC) : $(RXMAC).check
$(RXMAC).check: $(RXMAC).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 20 --dump-vcd $(RXMAC).vcd $(RXMAC).smt2
	$(SMTBMC)    $(INDARGS) -t 16 --dump-vcd $(RXMAC).vcd $(RXMAC).smt2
	$(SMTBMC) -g $(BMCARGS) -t 20 --dump-vcd $(RXMAC).vcd $(RXMAC).smt2
	touch $@

$(RXPAD) : $(RXPAD).check
$(RXPAD).check: $(RXPAD).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(RXPAD).vcd $(RXPAD).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(RXPAD).vcd $(RXPAD).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(RXPAD).vcd $(RXPAD).smt2
	touch $@

$(RXPRE) : $(RXPRE).check
$(RXPRE).check: $(RXPRE).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(RXPRE).vcd $(RXPRE).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(RXPRE).vcd $(RXPRE).smt2
	$(SMTBMC) -g $(BMCARGS) -t 40 --dump-vcd $(RXPRE).vcd $(RXPRE).smt2
	touch $@

$(RXIPK) : $(RXIPK).check
$(RXIPK).check: $(RXIPK).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(RXIPK).vcd $(RXIPK).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(RXIPK).vcd $(RXIPK).smt2
	$(SMTBMC) -c $(BMCARGS) -t 40 --dump-vcd $(RXIPK)%.vcd $(RXIPK).smt2
	touch $@

$(RXWRT) : $(RXWRT).check
$(RXWRT).check: $(RXWRT).smt2
	@rm -f $@
	$(SMTBMC)    $(BMCARGS) -t 40 --dump-vcd $(RXWRT).vcd $(RXWRT).smt2
	$(SMTBMC)    $(INDARGS) -t 36 --dump-vcd $(RXWRT).vcd $(RXWRT).smt2
	$(SMTBMC) -c $(BMCARGS) -t 40 --dump-vcd $(RXWRT)%.vcd $(RXWRT).smt2
	touch $@

.PHONY: clean
clean:
	rm -f $(TXCRC).smt2 $(TXCRC)*.vcd $(TXCRC).yslog
	rm -f $(TXPRE).smt2 $(TXPRE)*.vcd $(TXPRE).yslog
	rm -f $(TXPAD).smt2 $(TXPAD)*.vcd $(TXPAD).yslog
	rm -f $(TXMAC).smt2 $(TXMAC)*.vcd $(TXMAC).yslog
	rm -f $(RXCRC).smt2 $(RXCRC)*.vcd $(RXCRC).yslog
	rm -f $(RXPRE).smt2 $(RXPRE)*.vcd $(RXPRE).yslog
	rm -f $(RXPAD).smt2 $(RXPAD)*.vcd $(RXPAD).yslog
	rm -f $(RXMAC).smt2 $(RXMAC)*.vcd $(RXMAC).yslog
	rm -f $(RXIPK).smt2 $(RXIPK)*.vcd $(RXIPK).yslog
	rm -f $(RXWRT).smt2 $(RXWRT)*.vcd $(RXWRT).yslog
	rm -f *.check
