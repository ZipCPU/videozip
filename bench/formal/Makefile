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
TESTS := addecrc addemac addepad addepreamble
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
$(TXMAC): $(TXMAC)_prf/PASS $(TXMAC)_cvr/PASS
$(TXMAC)_prf/PASS: $(TXMAC).sby $(NETRTL)/$(TXMAC).v
	sby -f $(TXMAC).sby prf
$(TXMAC)_cvr/PASS: $(TXMAC).sby $(NETRTL)/$(TXMAC).v
	sby -f $(TXMAC).sby cvr

.PHONY: $(TXPAD)
$(TXPAD): $(TXPAD)_prf/PASS $(TXPAD)_cvr/PASS
$(TXPAD)_prf/PASS: $(TXPAD).sby $(NETRTL)/$(TXPAD).v
	sby -f $(TXPAD).sby prf
$(TXPAD)_cvr/PASS: $(TXPAD).sby $(NETRTL)/$(TXPAD).v
	sby -f $(TXPAD).sby cvr

.PHONY: $(TXPRE)
$(TXPRE): $(TXPRE)_prf/PASS $(TXPRE)_cvr/PASS
$(TXPRE)_prf/PASS: $(TXPRE).sby $(NETRTL)/$(TXPRE).v
	sby -f $(TXPRE).sby prf
$(TXPRE)_cvr/PASS: $(TXPRE).sby $(NETRTL)/$(TXPRE).v
	sby -f $(TXPRE).sby cvr

.PHONY: $(RXCRC)
$(RXCRC): $(RXCRC)_prf/PASS $(RXCRC)_cvr/PASS
$(RXCRC)_prf/PASS: $(RXCRC).sby $(NETRTL)/$(RXCRC).v
	sby -f $(RXCRC).sby prf
$(RXCRC)_cvr/PASS: $(RXCRC).sby $(NETRTL)/$(RXCRC).v
	sby -f $(RXCRC).sby cvr

.PHONY: $(RXMAC)
$(RXMAC): $(RXMAC)_prf/PASS $(RXMAC)_cvr/PASS
$(RXMAC)_prf/PASS: $(RXMAC).sby $(NETRTL)/$(RXMAC).v
	sby -f $(RXMAC).sby prf
$(RXMAC)_cvr/PASS: $(RXMAC).sby $(NETRTL)/$(RXMAC).v
	sby -f $(RXMAC).sby cvr

.PHONY: $(RXPRE)
$(RXPRE): $(RXPRE)_prf/PASS $(RXPRE)_cvr/PASS
$(RXPRE)_prf/PASS: $(RXPRE).sby $(NETRTL)/$(RXPRE).v
	sby -f $(RXPRE).sby prf
$(RXPRE)_cvr/PASS: $(RXPRE).sby $(NETRTL)/$(RXPRE).v
	sby -f $(RXPRE).sby cvr

.PHONY: $(RXPAD)
$(RXPAD): $(RXPAD)_prf/PASS $(RXPAD)_cvr/PASS
$(RXPAD)_prf/PASS: $(RXPAD).sby $(NETRTL)/$(RXPAD).v
	sby -f $(RXPAD).sby prf
$(RXPAD)_cvr/PASS: $(RXPAD).sby $(NETRTL)/$(RXPAD).v
	sby -f $(RXPAD).sby cvr

.PHONY: $(RXIPK)
$(RXIPK): $(RXIPK)_prf/PASS $(RXIPK)_cvr/PASS
$(RXIPK)_prf/PASS: $(RXIPK).sby $(NETRTL)/$(RXIPK).v
	sby -f $(RXIPK).sby prf
$(RXIPK)_cvr/PASS: $(RXIPK).sby $(NETRTL)/$(RXIPK).v
	sby -f $(RXIPK).sby cvr

.PHONY: $(RXWRT)
$(RXWRT): $(RXWRT)_prf/PASS $(RXWRT)_cvr/PASS
$(RXWRT)_prf/PASS: $(RXWRT).sby $(NETRTL)/$(RXWRT).v
	sby -f $(RXWRT).sby prf
$(RXWRT)_cvr/PASS: $(RXWRT).sby $(NETRTL)/$(RXWRT).v
	sby -f $(RXWRT).sby cvr

.PHONY: clean
clean:
	rm -rf $(TXCRC)/
	rm -rf $(TXPRE)_prf/ $(TXPRE)_cvr/
	rm -rf $(TXPAD)_prf/ $(TXPAD)_cvr/
	rm -rf $(TXMAC)_prf/ $(TXMAC)_cvr/
	rm -rf $(RXPRE)_prf/ $(RXPRE)_cvr/
	rm -rf $(RXCRC)_prf/ $(RXCRC)_cvr/
	rm -rf $(RXPAD)_prf/ $(RXPAD)_cvr/
	rm -rf $(RXMAC)_prf/ $(RXMAC)_cvr/
	rm -rf $(RXIPK)_prf/ $(RXIPK)_cvr/
	rm -rf $(RXWRT)_prf/ $(RXWRT)_cvr/
	rm -rf *.check
