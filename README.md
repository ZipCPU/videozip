# VideoZip

The Nexys Video board has now served me well through many funded, commercial
projects.  Many of these are SONAR projects, although there have been some
significant other projects as well--to include two separate graphics (HDMI)
projects.  The goal of this github project repository is to form a demonstration
baseline project from which a customer project, using the Nexys Video board,
can then be tailored.  As a result, part of the purpose of this project is
to demonstrate usage of all, or at least most, of the interfaces on the board.

1. GPIO and SPIO: The first step to any board control is to be able to control
   individual bits.  Some bits can be simply bit-banged.  A set of these
   have been grouped together for control via a GPIO controller.  A second
   set of bits is similar, but a "Special Purpose I/O" controller has been
   built for them.  These include the LEDs, buttons, and switches.

   Since all board debugging starts with blinky, I'll list these two
   capabilities first.

2. UART: One of the first and fundamental interfaces used on all my boards is
   the UART interface.  From that interface, other interfaces can be debugged.

3. EXBUS: This is my debugging bus interface.  This particular one is a 4th
   generation interface, using a binary encoding to allow an external host
   (PC) to read and write locations on the bus.  This version should be
   a (rough) 16% faster than the last one.  (No, that's not a great
   improvement, but 16% is still 16%.)

4. MegaNet: This is my term for a Gb Ethernet (GbE) interface that handles
   a lot of packets in hardware.  Automatically handled packets include
   ARP and ICMP.  Debug packets (if enabled) are forwarded to the debug
   interface.  Everything else gets sent to the CPU's virtual packet FIFO--if
   so enabled.

5. NEXBUS: This is basically the EXBUS interface, save that it runs over a
   Gb Ethernet interface.

   This has been ported from a SONAR design, where the only access to the
   FPGA was over the Ethernet port.

6. MDIO: I have a controller to interact with the Ethernet Management Data
   Input/Output interfaces associated with the Ethernet port.  This is more
   for demonstration purposes than anything else, but it is useful when you
   want to get a design up and running and you aren't necessarily sure what
   (if anything) is wrong with the Ethernet interface.

7. VIDPIPE: Demonstrates a basic HDMI pipeline.  Video may be brought in from
   an external source, or generated locally.  An overlay may be placed on top
   of it.  The result is then send to an external HDMI output.

   Unlike prior versions of the VideoZip project, this version is designed to
   handle subclock IO synchronization delays automatically.

8. I2C: A key component of several projects has now been my I2C CPU.  This is
   a basic I2C controller that can run off of a script in memory.  It was
   initially developed for handling telemetry without CPU involvement.  With
   CPU involvement, plus one or more pre-compiled memory scripts, it's becomes
   a very capable controller.

   The Nexys Video board essentially has three separate I2C busses: two for
   the HDMI ports, and a third one for controlling Audio.  Using the script,
   the CPU can run the script on any HDMI insertion to read and then forward
   EDID data from the downstream HDMI to the upstream HDMI, before then turning
   on the HDMI hotplug availability signal.

   Even though the I2C controller is meant for unattended operation, it does
   have the ability to accept manual control.  Hence, a CPU can still bit-bang
   the port if desired.

9. I2S Audio.  I've got an audio capability I built for a SONAR test.  I've
   used it, and so I know it works.  However, I'm not (yet) certain what I'll
   do for the demo project.

10. ZipCPU: Because of course.  As the saying goes, if all you have is a hammer,
   then the whole world looks like a nail.  Any problem that cannot be
   accomplished in RTL may then be accomplished by the ZipCPU in software.

11. QSPI Flash controller:  This is used for both configuring the FPGA, as well
   as loading software onto the ZipCPU.

12. DDR3 SDRAM:  My intent is to use an open source DDR3 controller, although
    for now the MIG DDR3 SDRAM controller works quite nicely.

13. SD Card:  I have an [SDIO based controller](rtl/sdspi/sdio.v), which will
    replace my [SPI based controller](rtl/sdspi/sdspi.v) as of this release.
    With the help of AutoFPGA, I should be able to maintain the ability to
    re-enable the [SPI based controller](rtl/sdspi/sdspi.v) again if I so
    choose.  Both will allow access to an SD Card.

    My plan is to also include the ZipCPU software necessary to read and write
    the SD Card here, to the point where it may be both tested and proven as
    part of this design.

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

14. ICAPE2:  My ICAPE2 controller provides access to the Xilinx's internal
    configuration access port.  I use this for two commands: setting the
    warm start address, and issuing IPROG requests to force the FPGA to reload
    itself.  This allows me to load the design once via JTAG, and ever
    after from the flash if desired.

    Other commands are available as well, just not as well used--such as
    reading the boot status and configuration register(s) to know the settings
    of the mode bits, or to know why a prior attempted FPGA configuration
    attempt failed.

15. Real Time Clock.  This ... is a basic real-time clock RTL.  It doesn't
    control an external clock, it doesn't run off of a battery, but it still
    generates a real time clock with subsecond level precision.  Three attached
    peripherals include a stop watch, timer, and an alarm based upon the real
    time clock.

    A separate real-time date component accompanies this clock.

    A separate GPS enabled real-time clock may also be used, although it
    requires set up (not included) and external hardware.

16. Wishbone SCOPE(s):  I tend not to use vendor tools, such as Vivado, for
    any debugging purposes.  If and when I need an ILA, I use my own--a
    Wishbone scope.  Looking around, you'll find several examples of how
    Wishbone Scopes have been used in this project to debug various interfaces
    along the way.

## Capabilities not currently included:

1. Mouse: A PS/2 capability to read from an attached mouse device has been
   removed, but may be added back into the design at a later time.

2. OLED: The Nexys Video has a black and white OLED attached to it.  I have a
   draft OLED control capability.  This draft capability hasn't been tested,
   and so it should be assumed to be non-functional at present.  I would like
   to build this capability further as time permits, since many of my
   commercial projects have wanted to use something like this.

