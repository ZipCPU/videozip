################################################################################
##
## Filename:	sw/board/Makefile
## {{{
## Project:	VideoZip, a ZipCPU SoC supporting video functionality
##
## Purpose:	
##
##
## Creator:	Dan Gisselquist, Ph.D.
##		Gisselquist Technology, LLC
##
################################################################################
## }}}
## Copyright (C) 2017-2024, Gisselquist Technology, LLC
## {{{
## This program is free software (firmware): you can redistribute it and/or
## modify it under the terms of the GNU General Public License as published
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
## }}}
## License:	GPL, v3, as defined and found on www.gnu.org,
## {{{
##		http://www.gnu.org/licenses/gpl.html
##
################################################################################
##
.PHONY: all
## }}}
PROGRAMS := cputest memtest simple_ping helloworld contest sdreadd sdrecord hdmistart logo
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
SUBMAKE:= $(MAKE) --no-print-directory -C
#
#
SOURCES := cputest.c memtest.c i2cdbg.c txfns.c helloworld.c simple_ping.c arp.c ipcksum.c sdinfo.c # hdmistart.c
HEADERS := $(foreach hdr,$(subst .c,.o,$(SOURCES)),$(wildcard $(hdr))) board.h
INCS    := -I../zlib -I../../rtl -I../fatfs -I.
LDSCRIPT:= -Tboard.ld
LBKRAM	:= -T bkram.ld -L../zlib
ZIPLIB	:= libvidzip.a
INSTALLD:=/home/dan/work/rnd/zipcpu/sw/install
NLIBD	:=$(INSTALLD)/cross-tools/zip/lib
LIB	:= $(NLIBD)/libg.a $(NLIBD)/libc.a
ZLIBD	:=../zlib
LFLAGS  := $(LDSCRIPT) -L../zlib -L../fatfs $(ZLIBD)/$(ZIPLIB)
LIBS    := -lc -lvidzip -lgcc
LIBFAT  := -lfatfs
FAT     := ../fatfs/libfatfs.a
CFLAGS  := -O3 $(INCS)
#
# For source analysis, the following macros are defined:
#

%.o: $(OBJDIR)/%.o
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -c $< -o $@
$(OBJDIR)/%.s: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) $(DUMPRTL) -S $< -o $@
$(OBJDIR)/%.txt: $(OBJDIR)/%.o
	$(mk-objdir)
	bash -c "$(RDELF) -a $^ ; $(OBJDUMP) -S -Drz $^ " | tee $@

%.txt: %
	$(OBJDUMP) -S -Drz $^ > $@


#
# The CPUTest program here is special--it doesn't use the C library.  Hence,
# it must have the -fno-builtin flag in order to build, and the -Tbkram.ld
# linker script to build something that doesn't go into flash but directly into
# RAM instead.
#
$(OBJDIR)/cputest.o: cputest.c board.h
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-nocis -fno-builtin $< -o $@
$(OBJDIR)/cputestcis.o: cputest.c board.h
	$(mk-objdir)
	$(CC) $(CFLAGS) -c -Wa,-cis -fno-builtin $< -o $@
$(OBJDIR)/cputest.s: cputest.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -S -Wa,-cis -fno-builtin $< -o $@

cputest: $(OBJDIR)/cputestcis.o board.ld $(ZLIBD)/$(ZIPLIB)
	# $(CC) $(CFLAGS) $(LFLAGS) $< $(LIBS) -o $@
	$(CC) $(CFLAGS) $(LBKRAM) $< $(LIBS) -o $@
## }}}

CONTESTSRC := contest.c txfns.c
CONTESTOBJ := $(addprefix $(OBJDIR)/,$(subst .c,.o,$(CONTESTSRC))) # $(DIVOBJ)
$(OBJDIR)/%.o: %.c
	$(mk-objdir)
	$(CC) $(CFLAGS) -I../host -c $< -o $@
contest: $(CONTESTOBJ) bkram.ld $(ZLIBD)/$(ZIPLIB)
	$(CC) $(LBKRAM) $(CFLAGS) $(CONTESTOBJ) $(LIBS) -o $@

memtest: $(OBJDIR)/memtest.o $(OBJDIR)/txfns.o bkram.ld $(ZLIBD)/$(ZIPLIB)
	$(CC) $(CFLAGS) $(LBKRAM) -Wl,-Map=$(OBJDIR)/memtest.map $(OBJDIR)/memtest.o $(OBJDIR)/txfns.o $(LIBS) -o $@

HDMISTARTOBJS:= $(addprefix $(OBJDIR)/,hdmistart.o txfns.o)
$(OBJDIR)/hdmistart.o: hdmistart.c
	$(mk-objdir)
	$(CC) -c $(CFLAGS) $< -o $@
hdmistart: $(HDMISTARTOBJS)
	$(CC) $(CFLAGS) $(LFLAGS) -Wl,-Map=$(OBJDIR)/hdmistart.map $(HDMISTARTOBJS) $(LIBS) -o $@

SDREADD:= $(addprefix $(OBJDIR)/,sdreadd.o txfns.o)
$(OBJDIR)/sdreadd.o: sdreadd.c
	$(mk-objdir)
	$(CC) -c $(CFLAGS) $< -o $@
sdreadd: $(SDREADD) board.ld $(FAT) $(ZLIBD)/$(ZIPLIB)
	$(CC) $(CFLAGS) $(LFLAGS) $(SDREADD) $(LIBFAT) $(LIBS) -o $@

SDRECORD:= $(addprefix $(OBJDIR)/,sdrecord.o txfns.o)
$(OBJDIR)/sdrecord.o: sdrecord.c
	$(mk-objdir)
	$(CC) -c $(CFLAGS) $< -o $@
sdrecord: $(SDRECORD) board.ld $(FAT) $(ZLIBD)/$(ZIPLIB)
	$(CC) $(CFLAGS) $(LFLAGS) $(SDRECORD) $(LIBFAT) $(LIBS) -o $@

helloworld: $(OBJDIR)/helloworld.o $(ZLIBD)/$(ZIPLIB)
	$(CC) $(CFLAGS) $(LFLAGS) $(OBJDIR)/helloworld.o -o $@

$(OBJDIR)/logo.o: logo.c logo.h
logo: $(OBJDIR)/logo.o $(OBJDIR)/txfns.o $(ZLIBD)/$(ZIPLIB)
	$(CC) $(CFLAGS) $(LFLAGS) $(OBJDIR)/logo.o $(OBJDIR)/txfns.o -o $@

simple_ping: $(OBJDIR)/simple_ping.o $(OBJDIR)/zipcpu.o
simple_ping: $(OBJDIR)/arp.o $(OBJDIR)/ipcksum.o
	$(CC) -Wl,-Map=simple_ping.map $(CFLAGS) $(LFLAGS) $^ -o $@


define	mk-objdir
	@bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR)/; fi"
endef

## tags
## {{{
tags: $(SOURCES) $(HEADERS)
	@echo "Generating tags"
	@ctags $(SOURCES) $(HEADERS)
## }}}

.PHONY: clean
## {{{
clean:
	rm -f $(PROGRAMS)
	rm -rf $(addsuffix .map,$(PROGRAMS))
	rm -rf $(addsuffix .txt,$(PROGRAMS))
	rm -rf $(OBJDIR)/
## }}}

.PHONY: depends
## {{{
define	build-depends
	@echo "Building dependency file(s)"
	$(mk-objdir)
	@$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	@sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	@rm $(OBJDIR)/xdepends.txt
endef

$(OBJDIR)/depends.txt: tags
	$(build-depends)

depends:
	$(build-depends)

ifneq ($(MAKECMDGOALS),clean)
-include $(OBJDIR)/depends.txt
endif
## }}}
