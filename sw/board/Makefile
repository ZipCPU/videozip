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
## Copyright (C) 2015, Gisselquist Technology, LLC
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
PROGRAMS := cputest i2cdbg # helloworld
all:	$(PROGRAMS)
#
#
OBJDIR  := obj-zip
NM      := zip-nm
RDELF   := zip-readelf
CC      := zip-gcc
OBJDUMP := zip-objdump
SOURCES := cputest.c i2cdbg.c helloworld.c
HEADERS := $(foreach hdr,$(subst .c,.o,$(SOURCES)),$(wildcard $(hdr))) board.h
LSCRIPT := -Tboard.ld
LFLAGS  := $(LSCRIPT)
CFLAGS  := -O3 -I../zlib -I../../rtl

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

$(OBJDIR)/cputest.o: cputest.c
	$(CC) -c $(CFLAGS) -Wa,-cis -fno-builtin $< -o $@
cputest: $(OBJDIR)/cputest.o boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/cputest.map $(OBJDIR)/cputest.o -o $@

$(OBJDIR)/i2cdbg.o: i2cdbg.c
	$(CC) -c $(CFLAGS) -Wa,-cis -fno-builtin $< -o $@
i2cdbg: $(OBJDIR)/i2cdbg.o boardram.ld
	$(CC) $(CFLAGS) -Tboardram.ld -Wl,-Map=$(OBJDIR)/i2cdbg.map $(OBJDIR)/i2cdbg.o -o $@

helloworld: $(OBJDIR)/helloworld.c
	$(CC) $(CFLAGS) $(LFLAGS) $(OBJDIR)/helloworld.c -o $@


define	mk-objdir
	bash -c "if [ ! -e $(OBJDIR) ]; then mkdir -p $(OBJDIR); fi"
endef

define	build-depends
	echo "Building dependency file(s)"
	$(mk-objdir)
	$(CC) $(CFLAGS) -MM $(SOURCES) > $(OBJDIR)/xdepends.txt
	sed -e 's/^.*.o: /$(OBJDIR)\/&/' < $(OBJDIR)/xdepends.txt > $(OBJDIR)/depends.txt
	rm $(OBJDIR)/xdepends.txt
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
	rm -rf $(OBJDIR)/ $(PROGRAMS) $(addsuffix .txt,$(PROGRAMS))

-include $(OBJDIR)/depends.txt
