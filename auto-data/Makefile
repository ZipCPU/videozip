################################################################################
##
## Filename:	Makefile
##
## Project:	VideoZip, a ZipCPU SoC supporting video functionality
##
## Purpose:	
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2017, Gisselquist Technology, LLC
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
.PHONY: all
all:	data install
#
# Could also depend upon load, if desired, but not necessary
DATA := global.txt bkram.txt buserr.txt clkcounter.txt clock.txt	\
	dlyarbiter.txt flash.txt gpio.txt hdmi.txt icape.txt mdio.txt	\
	pic.txt pwrcount.txt rtcdate.txt rtcgps.txt spio.txt	\
	version.txt wbmouse.txt wboledbw.txt wbpmic.txt busconsole.txt	\
	zipmaster.txt gps.txt
	# Not used: SDSPI

AUTOFPGA := ../../../autofpga/trunk/sw/autofpga

.PHONY: data
data: $(AUTOFPGA) $(DATA)
	$(AUTOFPGA) -o . $(DATA)

.PHONY: install
install: data
	$(call notify-on-change,toplevel.v,../rtl/)
	$(call notify-on-change,main.v,../rtl/)
	$(call notify-on-change,regdefs.h,../sw/host/)
	$(call notify-on-change,regdefs.cpp,../sw/host/)
	$(call notify-on-change,board.h,../sw/board/)
	$(call notify-on-change,board.ld,../sw/board/)

define	notify-on-change
	@bash -c 'cmp $(1) $(2)/$(1); if [[ $$? != 0 ]]; then echo "Files $(1) and $(2)/$(1) differ"; fi'
endef

