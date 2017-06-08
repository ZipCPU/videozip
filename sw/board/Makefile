################################################################################
##
## Filename:	sw/board/Makefile
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
PROGRAMS := cputest i2cdbg hdmistart hdmistest # readhist readframe # helloworld
all:	$(PROGRAMS)
#
#
CC	:=zip-gcc
AS	:=zip-as
LD	:=zip-ld
NM	:=zip-nm
OBJDIR	:= obj-zip
RDELF	:= zip-readelf
OBJDUMP := zip-objdump
SOURCES := cputest.c i2cdbg.c hdmistart.c hdmistest.c txfns.c helloworld.c readhist.c readframe.c
HEADERS := $(foreach hdr,$(subst .c,.o,$(SOURCES)),$(wildcard $(hdr))) board.h
LSCRIPT := -Tboard.ld
LFLAGS  := $(LSCRIPT)
INCS    := -I../zlib -I../../rtl -I.
CFLAGS  := -O3 $(INCS)
ZIPLIB	:= libvidzip.a
LIBS    := -lc -lvidzip
INSTALLD:=/home/dan/work/rnd/zipcpu/sw/install
NLIBD	:=$(INSTALLD)/cross-tools/zip/lib
ZLIBD	:=../zlib
LIB	:=$(ZLIBD)/libzbaic.a $(NLIBD)/libg.a $(NLIBD)/libc.a
#
# For source analysis, the following macros are defined:

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) $(DUMPRTL) -S $< -o $@
$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	$(mk-objdir)
	bash -c "$(RDELF) -a $^ ; $(OBJDDUMP) -S -D $^ " | tee $@
%.txt: %
	$(OBJDUMP) -S -D $^ > $@


#
# The CPUTest program here is special--it doesn't use the C library.  Hence,
# it must have the -fno-builtin flag in order to build, and the -Tartyram.ld
# linker script to build something that doesn't go into flash but directly into
# RAM instead.
#
$(OBJDIR)/cputest.o: cputest.c
	$(CC) $(CFLAGS) -c -Wa,-nocis -fno-builtin $< -o $@
$(OBJDIR)/cputestcis.o: cputest.c
	$(CC) $(CFLAGS) -c -Wa,-cis -fno-builtin $< -o $@
$(OBJDIR)/cputest.s: cputest.c
	$(CC) $(CFLAGS) -S -Wa,-cis -fno-builtin $< -o $@

cputest: $(OBJDIR)/cputest.o boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/cputest.map $(OBJDIR)/cputest.o -o $@

I2CDBGOBJS := $(addprefix $(OBJDIR)/,i2cdbg.o txfns.o)
$(OBJDIR)/i2cdbg.o: i2cdbg.c
	$(CC) -c $(CFLAGS) -fno-builtin $< -o $@
i2cdbg: $(I2CDBGOBJS) boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/i2cdbg.map $(I2CDBGOBJS) -o $@
	echo $(I2CDBGOBJS)

HDMISTARTOBJS:= $(addprefix $(OBJDIR)/,hdmistart.o txfns.o)
$(OBJDIR)/hdmistart.o: hdmistart.c
	$(CC) -c $(CFLAGS) -fno-builtin $< -o $@
hdmistart: $(HDMISTARTOBJS) boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/hdmistart.map $(HDMISTARTOBJS) -o $@

HDMISTESTOBJS:= $(addprefix $(OBJDIR)/,hdmistest.o txfns.o)
$(OBJDIR)/hdmistest.o: hdmistest.c
	$(CC) -c $(CFLAGS) -fno-builtin $< -o $@
hdmistest: $(HDMISTESTOBJS) boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/hdmistest.map $(HDMISTESTOBJS) -o $@

READHISTOBJS:= $(addprefix $(OBJDIR)/,hdmistest.o txfns.o)
$(OBJDIR)/readhist.o: readhist.c
	$(CC) -c $(CFLAGS) -fno-builtin $< -o $@
readhist: $(READHISTOBJS) boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/readhist.map $(READHISTOBJS) -o $@

READFRAMEOBJS:= $(addprefix $(OBJDIR)/,readframe.o txfns.o)
$(OBJDIR)/readframe.o: readframe.c
	$(CC) -c $(CFLAGS) -Wa,-cis -fno-builtin $< -o $@
readframe: $(READFRAMEOBJS) boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/readframe.map $(READFRAMEOBJS) -o $@

helloworld: $(OBJDIR)/helloworld.o
	$(CC) $(CFLAGS) $(LFLAGS) $(OBJDIR)/helloworld.o -o $@


define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef

define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
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

.PHONY: clean
clean:
	rm -f $(PROGRAMS)
	rm -rf $(addsuffix .map,$(PROGRAMS))
	rm -rf $(addsuffix .txt,$(PROGRAMS))
	rm -rf $(OBJDIR)/

-include $(OBJDIR)/depends.txt
