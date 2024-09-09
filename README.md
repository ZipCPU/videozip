# VideoZip

The Nexys Video board has now served me well through many funded, commercial
projects.  Many of these are SONAR projects, although there have been some
significant other projects as well--to include two separate graphics (HDMI)
projects.  The goal of this github project repository is to form a demonstration
baseline project from which a customer project, using the Nexys Video board,
can then be tailored.  As a result, part of the purpose of this project is
to demonstrate usage of all, or at least most, of the interfaces on the board.

## Capabilities

1. Debugging bus.  It's important to be able to interact with a board.  This
   interaction is possible via both UART and GbE network.

   Status: PASSES

1. GPIO and SPIO: The first step to any board control is to be able to control
   individual bits.  Some bits can be simply bit-banged.  A set of these
   have been grouped together for control via a GPIO controller.  A second
   set of bits is similar, but a "Special Purpose I/O" controller has been
   built for them.  These include the LEDs, buttons, and switches.

   Since all board debugging starts with blinky, I'll list these two
   capabilities first.

   Status: PASSES

2. UART: One of the first and fundamental interfaces used on all my boards is
   the UART interface.  From that interface, other interfaces can be debugged.

   Status: PASSES

3. EXBUS: This is my debugging bus interface.  This particular one is a 4th
   generation interface, using a binary encoding to allow an external host
   (PC) to read and write locations on the bus.  This version should be
   a (rough) 16% faster than the last one.  (No, that's not a great
   improvement, but 16% is still 16%.)

   Status: PASSES

4. MegaNet: This is my term for a Gb Ethernet (GbE) interface that handles
   a lot of packets in hardware.  Automatically handled packets include
   ARP and ICMP.  Debug packets (if enabled) are forwarded to the debug
   interface.  Everything else gets sent to the CPU's virtual packet FIFO--if
   so enabled.

   Status: PASSES

5. NEXBUS: This is basically the EXBUS interface, save that it runs over a
   Gb Ethernet interface.

   This has been ported from a SONAR design, where the only access to the
   FPGA was over the Ethernet port.

   Status: PASSES

6. MDIO: I have a controller to interact with the Ethernet Management Data
   Input/Output interfaces associated with the Ethernet port.  This is more
   for demonstration purposes than anything else, but it is useful when you
   want to get a design up and running and you aren't necessarily sure what
   (if anything) is wrong with the Ethernet interface.

   Status: PASSES

7. VIDPIPE: Demonstrates a basic HDMI pipeline.  Video may be brought in from
   an external source, or generated locally.  An overlay may be placed on top
   of it.  The result is then send to an external HDMI output.

   Unlike prior versions of the VideoZip project, this version is designed to
   handle subclock IO synchronization delays automatically.

   Status: FAILS, still under investigation

8. [I2C](rtl/wbi2c/wbi2ccpu.v): A key component of several projects has now
   been my "[I2C CPU](https://github.com/ZipCPU/wbi2c)".  This is
   a basic I2C controller that can run off of a script kept in memory.  It was
   initially developed for handling telemetry without CPU involvement.  With
   CPU involvement, plus one or more pre-compiled memory scripts, it's becomes
   a very capable controller.

   The Nexys Video board essentially has three separate I2C busses: two for
   the HDMI ports, and a third one for controlling Audio.  Using the script,
   the CPU can run a basic script on any HDMI insertion to read and then
   forward EDID data from the downstream HDMI to the upstream HDMI, before
   then turning on the HDMI hotplug availability signal.

   Even though the I2C controller is meant for unattended operation, it does
   have the ability to accept manual control.  Hence, a CPU can still bit-bang
   the port if desired.

   Status: PASSES (Although it looks like the HDMI might require a special
   capability.)

9. [I2S Audio](rtl/audio/axisi2s.v).  I've got an audio capability I built
   for a SONAR test.  I've used it, and so I know it works.  However, I'm not
   (yet) certain what I'll do with it for the demo project.

   Status: Not (yet) tested.

10. [ZipCPU](https://github.com/ZipCPU/zipcpu): Because of course.  As the
    saying goes, if all you have is a hammer, then the whole world looks like
    a nail.  Any problem that cannot be accomplished in RTL may then be
    accomplished by the ZipCPU in software.

    Status: PASSES.

11. QSPI Flash controller:  This is used for both configuring the FPGA, as well
    as loading software onto the ZipCPU.

    Status: PASSES

12. DDR3 SDRAM:  My intent is to use an open source DDR3 controller, although
    for now the MIG DDR3 SDRAM controller works quite nicely.

    Status: MIG DDR3 controller PASSES.  UberDDR3, not yet tested.

13. [SD Card](rtl/sdspi/sdio.v):  I have an
    [SDIO based controller](rtl/sdspi/sdio.v), which will replace my
    [SPI based controller](rtl/sdspi/sdspi.v) as of this release.  With the
    help of [AutoFPGA](https://github.com/ZipCPU/autofpga), I should be able to
    maintain the ability to re-enable the [SPI based
    controller](rtl/sdspi/sdspi.v) again if I so choose.  Both will allow
    access to an SD Card.

    My plan is to also include the ZipCPU [software necessary to read and write
    the SD Card here](sw/fatfs/sdiodrv.c), to the point where it may be both
    tested and proven as part of this design.

    Even better, I have the ability to read and load software from an SD card
    on startup.  This capability can go so far as to load a flash configuration
    on startup as well.  Hence, the design can start from a current flash load,
    run a small program in ROM to load a bigger program from the SD card into
    main memory, run that program, load a design configuration (i.e. bit file)
    from the SD card to flash, perhaps even loading a ZipCPU program to the
    flash as well, and then reconfigure the FPGA from flash (via the ICAPE2
    controller), so that it also starts the ZipCPU program that had been
    (just now) copied from the SD card to flash.  In the past, this approach
    has been very useful for deploying FPGA designs to customers who don't have
    access to the Vivado JTAG loader.

    Status: SD Card PASSES, automatic boot is not (yet) tested.

14. [ICAPE2](rtl/wbicapetwo.v):  My [ICAPE2 controller](rtl/wbicapetwo.v)
    provides access to the Xilinx's internal
    configuration access port.  I use this for two commands: setting the
    warm start address, and issuing IPROG requests to force the FPGA to reload
    itself.  This allows me to load the design once via JTAG, and ever
    after from the flash if desired.

    Other commands are available as well, just not as well used--such as
    reading the boot status and configuration register(s) to know the settings
    of the mode bits, or to know why a prior attempted FPGA configuration
    attempt failed.

    Status: Worked here long ago, not tested in a while.

15. [Real Time Clock](rtl/rtc/rtclight.v).  This ... is a basic real-time clock
    RTL.  It doesn't control an external clock, it doesn't run off of a
    battery, but it still generates a real time clock with subsecond level
    precision.  Three attached peripherals include a
    [stop watch](rtl/rtc/rtcstopwatch.v),
    [timer](rtl/rtc/rtctimer.v), and an
    [alarm](rtl/rtc/rtcalarm.v) based upon the real
    time clock.

    A separate [real-time date](rtl/rtc/rtcdate.v) component accompanies this clock.

    A separate [GPS enabled real-time clock](rtl/rtc/rtcgps.v) may also be
    used, although it requires set up (not included), external hardware,
    and some software to get the actual time.

    Status: Not (yet) tested.

16. [Wishbone SCOPE(s)](rtl/wbscope/wbscope.v):  I tend not to use vendor
    tools, such as Vivado, for any debugging purposes.  If and when I need an
    ILA, I use my own--a Wishbone scope.  Looking around, you'll find several
    examples of how Wishbone Scopes have been used in this project to debug
    various interfaces along the way.

    Status: PASSES

17. [SPI CPU](rtl/wbspi/spicpu.v): Very similar to the I2C CPU is a SPI
    CPU capability.  As with the I2C CPU, this can accept and run a script
    from memory.  This component is currently wired up to control the OLED
    present on the Nexys Video board.

    Status: PASSES

## Capabilities not currently included:

1. Mouse: A PS/2 capability to read from an attached mouse device has been
   removed, but may be added back into the design at a later time.

## Basic Operation

To reconfigure or adjust the configuration of the design, adjust the components
used on the AutoFPGA command line.  These are found and defined in the
[autodata/Makefile](autodata/Makefile).  This will control which components are
currently part of the design and which are not.  To reconfigure the design for
the new component set, simply then run:

    make autodata

This will recompose the bus, assign addresses as necessary, and rebuild the
[toplevel](rtl/toplevel.v) and [main](rtl/main.v) design components.  From
there, everything else needs to know what components are part of the board,
which are built into the design, etc.  Hence this will also adjust the register
mapping files in [regdefs.h](sw/host/regdefs.h) and
[regdefs.cpp](sw/host/regdefs.cpp), rebuild the linker script(s) such as
[board.ld](sw/host/board.ld), and rebuild a board definition file,
[board.h](sw/host/board.h) used by the ZipCPU.

From here, you can build a Verilog simulation via:

    make rtl
    make sim

You can then run the simulation via:

    cd sim; ./main_tb [-d] [-d] [-g] [zipcpu_program]

Options include:

- `-d` generates a trace file, whose output is controlled by the GPIO
  peripheral, allowing the CPU to determine when data gets dumped and not.

- `-d -d` forces the trace file generation for all cycles, independent of CPU control.

- `-g` turns on an active simulation of the HDMI port.

- `zipcpu_program` will pre-load the flash and/or SDRAM with the given ZipCPU
  program and run it in simulation.

While the simulation is running, you can use

    telnet localhost 6783

to open a console port to the ZipCPU.

If you wish to interact with the simulation, you'll first want to build the
host access capabilities:

    make sw-host

and then set the `VIDEODEV` environment variable.  It may be set to either:

    export VIDEODEV=sim://localhost

or

    export VIDEODEV=net://localhost

depending upon whether or not you wish to access the design via the simulated
serial port, or a simulated network port.

Once done, you can use any of the programs in `sw/host` to interact with the
design.  Most common, you would use `exregs` to read and write registers
within the design.  For example, the followiong will read a variety of
registers from within the design.

    exregs VERSION
    exregs BUILDTIME
    exregs GPIO
    exregs SDRAM

The full list of named registrs can be found in
[regdefs.cpp](sw/host/regdefs.cpp).


If you wish to build the design and load it onto hardware, the same interface
is available but the setup is just a touch different.

To use the serial port to access the design, you'll first need to run
[exuart](sw/host/exuart.v).  This program connects to the serial port and
forwards everything it hears to a TCP/IP port on your computer.  The
program accepts one argument specifying the terminal device your PCB
is connected to, such as:

    exuart /dev/ttyUSB2

Once this program starts, you'll want to leave it running.  You can then
adjust the environment to:

    export VIDEODEV=uart://localhost

Once done, the same access commands should then work again only now they
would interact with the device itself instead of the simulation.

While [exuart](sw/host/exuart.cpp) is running, you may still access the
console port of the ZipCPU running on the Nexys Video board the same way
as before:

    telnet localhost 6783

You can also interact with the design independent of the console port via
its Gb Ethernet port.  To do this, you'll need the board's IP address.
This is currently set in [autodata/meganet.txt](autodata/meganet.txt).  As of
this writing, the IP address is fixed at `192.168.15.29`, but can easily be
changed there.  Assuming you keep this IP address the same, you'll need to
let the software know where to find it:

    export VIDEODEV=net://192.168.15.29

Once done, the host commands, such as [exbus](sw/host/exbus.cpp), should work
again.

One very useful command is the [zipload](sw/host/zipload.cpp) command.  This
command loads ZipCPU software onto the board--whether to RAM or flash, as
determined by the linker script used to build the program.  If given the `-r`
option, [zipload](sw/host/zipload.cpp) will also start the ZipCPU running
the given program as well.

Particular demonstration programs include:

- [cputest](sw/board/cputest.c): Simply tests the ZipCPU, making sure all the
  instructions work.

- [contest](sw/board/contest.c): Looks for all of the various peripherals that
  have been built into the board, and attempts to verify that the CPU can reach
  out and touch each of them.

- [hdmistart](sw/board/hdmistart.c): Attempts to fire up the HDMI.  This involves:
  1. Waiting for the downstream HDMI hotplug to be asserted
  2. Reading the EDID information from the downstream HDMI (transmit)
     connection
  3. Moving that EDID info to an upstream I2C slave
  4. Turning on the hot plug assertion for the upstream
  5. Waiting for the upstream (HDMI receive) connection to be valid
  6. Measuring the HDMI clock speed
  7. Forwarding the incoming HDMI downstream.

  If all goes well, then whatever comes into the device HDMI-wise should also
  be transmitted out.  It's at this point that I'd like to come back and
  investigate the HDMI data island packets.

- [helloworld](sw/board/helloworld.c): A basic program, built upon the
  C-library, that just prints "Hello, World!" to the console port.

- [logo](sw/board/logo.c): Puts a couple of logos on the B/W OLED, to include my handsome mug.  This demonstrates that the (write-half of the) SPI controller works.

- [memtest](sw/board/memtest.c): Tests the DDR3 SDRAM memory.

- [sdreadd](sw/board/sdreadd.c): Verifies that the directory of the SD card can
  be read from.

- [sdrecord](sw/board/sdrecord.c): Writes data to the SD card, and then reads it back again--measuring the speed of both write and read operations.  The output should look [something like this](doc/sdrecord-spd.png).

## Status

The design is currently coming out of a massive rewrite.  Those simulations
that have been built, work.  It's now time for hardware testing.

Test results:

- [Connection testing](sw/board/contest.c) and [CPU testing](sw/board/cputest.c)
  work.

- [helloworld](sw/board/helloworld.c) also works.  This test involves first
  programming the flash as well.

- [Controlling the B/W OLED](sw/board/logo.c) works nicely.

  The next step here will be to create a glyph library, and the ability to
  write text to the OLED to provide user feedback.

- Hardware network connectivity (ARP+ICMP) works nicely

  I haven't (yet) verified that the CPU can access the network.

- Both reading and writing the SD card works

- Reading and forwarding EDID information just works

  But ... I haven't managed to get the upstream HDMI generator to provide a clock (yet).  This is an issue for active debugging.  It appears to indicate an EDID problem associated with a separate device address, the segment address at 0x60, and not just the standard EDID address of 0xa0/0xa1.

## License

This project is released under the GPL v3.  Should this license be insufficient
for your needs, please contact Gisselquist Technology, LLC, to discuss other
options.

