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
## Copyright (C) 2017-2019, Gisselquist Technology, LLC
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

.PHONY: $(TXCRC)
$(TXCRC): $(TXCRC)/PASS
$(TXCRC)/PASS: $(TXCRC).sby $(NETRTL)/$(TXCRC).v
	sby -f $(TXCRC).sby

.PHONY: $(TXMAC)
$(TXMAC): $(TXMAC)/PASS
$(TXMAC)/PASS: $(TXMAC).sby $(NETRTL)/$(TXMAC).v
	sby -f $(TXMAC).sby

.PHONY: $(TXPAD)
$(TXPAD): $(TXPAD)/PASS
$(TXPAD)/PASS: $(TXPAD).sby $(NETRTL)/$(TXPAD).v
	sby -f $(TXPAD).sby

.PHONY: $(TXPRE)
$(TXPAD): $(TXPRE)/PASS
$(TXPRE)/PASS: $(TXPRE).sby $(NETRTL)/$(TXPRE).v
	sby -f $(TXPRE).sby

.PHONY: $(RXCRC)
$(RXCRC): $(RXCRC)/PASS
$(RXCRC)/PASS: $(RXCRC).sby $(NETRTL)/$(RXCRC).v
	sby -f $(RXCRC).sby

.PHONY: $(RXMAC)
$(RXMAC): $(RXMAC)_prf/PASS $(RXMAC)_cvr/PASS
$(RXMAC)_prf/PASS: $(RXMAC).sby $(NETRTL)/$(RXMAC).v
	sby -f $(RXMAC).sby prf
$(RXMAC)_cvr/PASS: $(RXMAC).sby $(NETRTL)/$(RXMAC).v
	sby -f $(RXMAC).sby cvr

.PHONY: $(RXPRE)
$(RXPRE): $(RXPRE)/PASS
$(RXPRE)/PASS: $(RXPRE).sby $(NETRTL)/$(RXPRE).v
	sby -f $(RXPRE).sby

.PHONY: $(RXPAD)
$(RXPAD): $(RXPAD)/PASS
$(RXPAD)/PASS: $(RXPAD).sby $(NETRTL)/$(RXPAD).v
	sby -f $(RXPAD).sby

.PHONY: $(RXIPK)
$(RXIPK): $(RXIPK)/PASS
$(RXIPK)/PASS: $(RXIPK).sby $(NETRTL)/$(RXIPK).v
	sby -f $(RXIPK).sby

.PHONY: $(RXWRT)
$(RXWRT): $(RXWRT)/PASS
$(RXWRT)/PASS: $(RXWRT).sby $(NETRTL)/$(RXWRT).v
	sby -f $(RXWRT).sby

.PHONY: clean
clean:
	rm -rf $(TXCRC)/ $(TXPRE)/ $(TXPAD)/ $(TXMAC)/
	rm -rf $(RXCRC)/ $(RXPRE)/ $(RXPAD)/ $(RXMAC)_prf/ $(RXMAC)_cvr/
	rm -rf $(RXIPK)/ $(RXWRT)/
	rm -rf *.check
