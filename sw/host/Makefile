################################################################################
##
## Filename:	Makefile
##
## Project:	VideoZip, a ZipCPU SoC supporting video functionality
##
## Purpose:	
## Targets:	
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
##
## Copyright (C) 2015-2019, Gisselquist Technology, LLC
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
PROGRAMS := wbregs netuart rdclocks mkedid zipload zipstate zipdbg cpedid \
	rdsync getframe manping flashid readmdio netstat
SCOPES := edidrxscope edidtxscope rawdscope tmdscope zipscope erxscope etxscope flashscope
all: $(PROGRAMS) $(SCOPES) gps
CXX := g++
OBJDIR := obj-pc
BUSSRCS := ttybus.cpp llcomms.cpp regdefs.cpp byteswap.cpp
SOURCES := wbregs.cpp netuart.cpp rdclocks.cpp flashdrvr.cpp		\
	 mkedid.cpp $(BUSSRCS)	edidrxscope.cpp	edidtxscope.cpp		\
	zipload.cpp zipstate.cpp zipdbg.cpp cpedid.cpp readhist.cpp	\
	getframe.cpp rawdscope.cpp tmdscope.cpp rdsync.cpp manping.cpp	\
	erxscope.cpp etxscope.cpp flashscope.cpp flashid.cpp		\
	readmdio.cpp mdioscope.cpp netstat.cpp
	# wbsettime.cpp
HEADERS := llcomms.h port.h ttybus.h devbus.h
OBJECTS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(SOURCES)))
BUSOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(BUSSRCS)))
CFLAGS := -g -Wall -I. -I../../rtl
LIBS :=
SUBMAKE := $(MAKE) --no-print-directory -C

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.cpp
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CXX) $(CFLAGS) -c $< -o $@

.PHONY: gps
gps: $(BUSOBJS) # $(OBJDIR)/scopecls.o
	@bash -c "if [[ -e gps/Makefile ]]; then $(SUBMAKE) gps; fi"

.PHONY: clean
clean:
	rm -rf $(OBJDIR)/ $(PROGRAMS) a.out

$(OBJDIR)/scopecls.o:    scopecls.cpp    scopecls.h
$(OBJDIR)/edidrxscope.o: edidrxscope.cpp scopecls.h
$(OBJDIR)/edidtxscope.o: edidtxscope.cpp scopecls.h
$(OBJDIR)/rawdscope.o:   rawdscope.cpp   scopecls.h
$(OBJDIR)/tmdscope.o:    tmdscope.cpp    scopecls.h
$(OBJDIR)/erxscope.o:    erxscope.cpp    scopecls.h
$(OBJDIR)/etxscope.o:    etxscope.cpp    scopecls.h
$(OBJDIR)/flashscope.o:  flashscope.cpp  scopecls.h
$(OBJDIR)/mdioscope.o:   mdioscope.cpp   scopecls.h
#
$(OBJDIR)/dumpflash.o:   dumpflash.cpp   regdefs.h
$(OBJDIR)/readmdio.o:    readmdio.cpp    regdefs.h
$(OBJDIR)/netstat.o:     netstat.cpp     scopecls.h

netuart: $(OBJDIR)/netuart.o
	$(CXX) $(CFLAGS) $^ -o $@
#
# Some simple programs that just depend upon the ability to talk to the FPGA,
# and little more. 
#manping: $(OBJDIR)/manping.o $(BUSOBJS)
#	$(CXX) $(CFLAGS) $^ -o $@
zipstate: $(OBJDIR)/zipstate.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@
wbregs: $(OBJDIR)/wbregs.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@
rdclocks: $(OBJDIR)/rdclocks.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@
rdsync: $(OBJDIR)/rdsync.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@
dumpflash: $(OBJDIR)/dumpflash.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ $(LIBS) -o $@
mkedid: $(OBJDIR)/mkedid.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
cpedid: $(OBJDIR)/cpedid.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
readhist: $(OBJDIR)/readhist.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
getframe: $(OBJDIR)/getframe.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
manping: $(OBJDIR)/manping.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
flashid: $(OBJDIR)/flashid.o $(BUSOBJS) $(OBJDIR)/flashdrvr.o
	$(CXX) $(CFLAGS) $^ -o $@
readmdio: $(OBJDIR)/readmdio.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@
netstat: $(OBJDIR)/netstat.o $(BUSOBJS)
	$(CXX) $(CFLAGS) $^ -o $@

#
# Programs that depend upon not just the bus objects, but the flash driver
# as well.
wbprogram: $(OBJDIR)/wbprogram.o $(OBJDIR)/flashdrvr.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
zipload: $(OBJDIR)/zipload.o $(OBJDIR)/flashdrvr.o $(BUSOBJS) $(OBJDIR)/zipelf.o
	$(CXX) -g $^ -lelf -o $@


## SCOPES
# These depend upon the scopecls.o, the bus objects, as well as their
# main file(s).
edidrxscope: $(OBJDIR)/edidrxscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
edidtxscope: $(OBJDIR)/edidtxscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
rawdscope: $(OBJDIR)/rawdscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
tmdscope: $(OBJDIR)/tmdscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
zipscope: $(OBJDIR)/zipscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
erxscope: $(OBJDIR)/erxscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
etxscope: $(OBJDIR)/etxscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
flashscope: $(OBJDIR)/flashscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@
mdioscope: $(OBJDIR)/mdioscope.o $(OBJDIR)/scopecls.o $(BUSOBJS)
	$(CXX) -g $^ -o $@

#
DBGSRCS  := zopcodes.cpp twoc.cpp
DBGOBJS := $(addprefix $(OBJDIR)/,$(subst .cpp,.o,$(DBGSRCS)))
zipdbg: $(OBJDIR)/zipdbg.o $(BUSOBJS) $(DBGOBJS)
	$(CXX) -g $^ -lcurses -o $@

define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	$(CXX) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)

.PHONY: depends
depends: tags
	$(build-depends)

$(OBJDIR)/depends.txt: $(SOURCES) $(HEADERS)
	$(build-depends)

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
