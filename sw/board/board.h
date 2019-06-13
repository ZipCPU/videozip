////////////////////////////////////////////////////////////////////////////////
//
// Filename:	./board.h
//
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// DO NOT EDIT THIS FILE!
// Computer Generated: This file is computer generated by AUTOFPGA. DO NOT EDIT.
// DO NOT EDIT THIS FILE!
//
// CmdLine:	autofpga autofpga -d -o . allclocks.txt genclk.txt netclockctr.txt global.txt dlyarbiter.txt icape.txt version.txt buserr.txt pic.txt pwrcount.txt xpander.txt vidarbiter.txt spio.txt gpio.txt rtcgps.txt rtcdate.txt wbuconsole.txt bkram.txt nflash.txt sdvidram.txt zipmaster.txt mdio.txt enet.txt gps.txt sdspi.txt hdmi.txt cpuscope.txt enetscope.txt mem_bkram_only.txt mem_flash_bkram.txt clkcounter.txt wbmouse.txt wbpmic.txt xdc.txt
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2017-2019, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#ifndef	BOARD_H
#define	BOARD_H

// And, so that we can know what is and isn't defined
// from within our main.v file, let's include:
#include <design.h>

#include <design.h>
#include <cpudefs.h>

#define	_HAVE_ZIPSYS
#define	PIC	_zip->z_pic

#ifdef	INCLUDE_ZIPCPU
#ifdef INCLUDE_DMA_CONTROLLER
#define	_HAVE_ZIPSYS_DMA
#endif	// INCLUDE_DMA_CONTROLLER
#ifdef INCLUDE_ACCOUNTING_COUNTERS
#define	_HAVE_ZIPSYS_PERFORMANCE_COUNTERS
#endif	// INCLUDE_ACCOUNTING_COUNTERS
#endif // INCLUDE_ZIPCPU



typedef	struct	EDID_SRC_S {
	unsigned	o_cmd;
	unsigned	o_spd;
	unsigned	o_ignored[64-2];
	unsigned	o_data[64];
} EDID_SRC;

#define	READ_EDID(START,LN)	((0xa1<<16)|(((START)&0x0ff)<<8)|((LN)&0x0ff))
#define	EDID_SRC_BUSY	0x80000000
#define	EDID_SRC_ERR	0x40000000



typedef	struct	GPSTRACKER_S	{
	unsigned	g_alpha, g_beta, g_gamma, g_step;
} GPSTRACKER;


typedef	struct	GPSTB_S	{
	unsigned	tb_maxcount, tb_jump;
	unsigned long	tb_err, tb_count, tb_step;
} GPSTB;


#ifndef	SCOPE_H
#define	SCOPE_H

typedef	struct	SCOPE_S {
	unsigned s_ctrl, s_data;
} SCOPE;
#endif


// Network packet interface
#define	ENET_TXGO		0x004000
#define	ENET_TXBUSY		0x004000
#define	ENET_NOHWCRC		0x008000
#define	ENET_NOHWMAC		0x010000
#define	ENET_RESET		0x020000
#define	ENET_NOHWIPCHK		0x040000
#define	ENET_TXCMD(LEN)		((LEN)|ENET_TXGO)
#define	ENET_TXCLR		0x038000
#define	ENET_TXCANCEL		0x000000
#define	ENET_RXAVAIL		0x004000
#define	ENET_RXBUSY		0x008000
#define	ENET_RXMISS		0x010000
#define	ENET_RXERR		0x020000
#define	ENET_RXCRC		0x040000	// Set on a CRC error
#define	ENET_RXLEN		rxcmd & 0x0ffff
#define	ENET_RXCLR		0x004000
#define	ENET_RXBROADCAST	0x080000
#define	ENET_RXCLRERR		0x078000
#define	ENET_TXBUFLN(NET)	(1<<(NET.txcmd>>24))
#define	ENET_RXBUFLN(NET)	(1<<(NET.rxcmd>>24))
typedef	struct ENETPACKET_S {
	unsigned	n_rxcmd, n_txcmd;
	unsigned long	n_mac;
	unsigned	n_rxmiss, n_rxerr, n_rxcrc, n_txcol;
} ENETPACKET;

#define	SYSINT_ENETRX	SYSINT(9)
#define	SYSINT_ENETTX	SYSINT(8)



#define	SYSPIC(A)	(1<<(A))


#define	ALTPIC(A)	(1<<(A))


#define WBMIC_ENABLE	0
#define WBMIC_DISABLE	(1<<20)
#define WBMIC_NONEMPTY	0
#define WBMIC_HALFINT	(1<<22)
#define WBMIC_RESET	(1<<24)

typedef struct  WBMIC_S {
	unsigned	m_data;
	unsigned	m_setup;
} WBMIC;


//
// GPIO input wires
//
#define	GPIO_HDMI_IN_CEC	0x000010000
#define	GPIO_HDMI_OUT_CEC	0x000020000
#define	GPIO_SD_DETECTED	0x000040000
#define	GPIO_HDMI_OUT_DETECT	0x000080000
#define	GPIO_GPS_3DF		0x000100000
#define	GPIO_SYSCLK_LOCKED	0x000200000
//
// GPIO output wires
//
#define	GPIO_SET(WIRE)	(((WIRE)<<16)|(WIRE))
#define	GPIO_CLR(WIRE)	 ((WIRE)<<16)
//
#define	GPIO_HDMI_IN_CEC_SET	0x000010001
#define	GPIO_HDMI_IN_CEC_CLR	0x000010000
#define	GPIO_HDMI_OUT_CEC_SET	0x000020002
#define	GPIO_HDMI_OUT_CEC_CLR	0x000020000
#define	GPIO_EDID_SCL		0x000000004
#define	GPIO_EDID_SDA		0x000000008
//
#define	GPIO_HDMI_IN_ENB	0x000000010
#define	GPIO_HDMI_IN_HPA	0x000000020
#define	GPIO_SD_RESET		0x000000040
#define	GPIO_HDMI_OUT_EN	0x000000080
//
#define	GPIO_EDID_SCL_SET	GPIO_SET(GPIO_EDID_SCL)
#define	GPIO_EDID_SCL_CLR	GPIO_CLR(GPIO_EDID_SCL)
#define	GPIO_EDID_SDA_SET	GPIO_SET(GPIO_EDID_SDA)
#define	GPIO_EDID_SDA_CLR	GPIO_CLR(GPIO_EDID_SDA)
#define	GPIO_HDMI_IN_ENB_SET	GPIO_SET(GPIO_HDMI_IN_ENB)
#define	GPIO_HDMI_IN_ENB_CLR	GPIO_CLR(GPIO_HDMI_IN_ENB)
#define	GPIO_HDMI_IN_HPA_SET	GPIO_SET(GPIO_HDMI_IN_HPA)
#define	GPIO_HDMI_IN_HPA_CLR	GPIO_CLR(GPIO_HDMI_IN_HPA)
#define	GPIO_SD_RESET_SET	GPIO_SET(GPIO_SD_RESET)
#define	GPIO_SD_RESET_CLR	GPIO_CLR(GPIO_SD_RESET)
#define	GPIO_HDMI_OUT_EN_SET	GPIO_SET(GPIO_HDMI_OUT_EN)
#define	GPIO_HDMI_OUT_EN_CLR	GPIO_CLR(GPIO_HDMI_OUT_EN)


// Mouse definitions
typedef struct  WBMOUSE_S {
	unsigned	m_bus, m_raw, m_screen, m_size;
} WBMOUSE;


#ifndef WBSCOPE_H
#define WBSCOPE_H

#define WBSCOPE_NO_RESET        0x80000000u
#define WBSCOPE_TRIGGER         (WBSCOPE_NO_RESET|0x08000000u)
#define WBSCOPE_MANUAL          (WBSCOPE_TRIGGER)
#define WBSCOPE_DISABLE         0x04000000u

typedef struct WBSCOPE_S {
        unsigned s_ctrl, s_data;
} WBSCOPE;
#endif


#ifndef	WBSCOPE_H
#define	WBSCOPE_H

#define	WBSCOPE_NO_RESET	0x800000000
#define	WBSCOPE_TRIGGER		(WBSCOPE_NO_RESET|0x08000000)
#define	WBSCOPE_MANUAL		(WBSCOPE_TRIGGER)
#define	WBSCOPE_DISABLE		0x04000000

typedef struct WBSCOPE_S {
	unsigned s_ctrl, s_data;
} WBSCOPE;
#endif


// Offsets for the ICAPE2 interface
#define	CFG_CRC		0
#define	CFG_FAR		1
#define	CFG_FDRI	2
#define	CFG_FDRO	3
#define	CFG_CMD		4
#define	CFG_CTL0	5
#define	CFG_MASK	6
#define	CFG_STAT	7
#define	CFG_LOUT	8
#define	CFG_COR0	9
#define	CFG_MFWR	10
#define	CFG_CBC		11
#define	CFG_IDCODE	12
#define	CFG_AXSS	13
#define	CFG_COR1	14
#define	CFG_WBSTAR	16
#define	CFG_TIMER	17
#define	CFG_BOOTSTS	22
#define	CFG_CTL1	24
#define	CFG_BSPI	31


#ifndef	WBUART_H
#define	WBUART_H

#define UART_PARITY_NONE        0
#define UART_HWFLOW_OFF         0x40000000
#define UART_PARITY_ODD         0x04000000
#define UART_PARITY_EVEN        0x05000000
#define UART_PARITY_SPACE       0x06000000
#define UART_PARITY_MARK        0x07000000
#define UART_STOP_ONEBIT        0
#define UART_STOP_TWOBITS       0x08000000
#define UART_DATA_8BITS         0
#define UART_DATA_7BITS         0x10000000
#define UART_DATA_6BITS         0x20000000
#define UART_DATA_5BITS         0x30000000
#define UART_RX_BREAK           0x0800
#define UART_RX_FRAMEERR        0x0400
#define UART_RX_PARITYERR       0x0200
#define UART_RX_NOTREADY        0x0100
#define UART_RX_ERR             (-256)
#define UART_TX_BUSY            0x0100
#define UART_TX_BREAK           0x0200

typedef struct  WBUART_S {
	unsigned	u_setup;
	unsigned	u_fifo;
	unsigned	u_rx, u_tx;
} WBUART;

#endif	// WBUART_H



#define BUSPIC(X) (1<<X)


typedef	struct	HDMI_IN_S {
	unsigned	hin_frame_addr;
	unsigned	hin_origin,
			hin_maxsz,
			hin_unused;
	unsigned	hin_ctrl, hin_manual, hin_syncdata, hin_quality;
	unsigned	hin_pixclk;
	unsigned	hin_reserved[3];
	short		hin_htotal, hin_ncols,
			hin_vtotal, hin_nrows;
	short		hin_hsstart, hin_ssend,
			hin_vsstart, hin_vssend;
} HDMI_IN;


typedef	struct	RTCLIGHT_S	{
	unsigned	r_clock, r_stopwatch, r_timer, r_alarm;
} RTCLIGHT;


#define	CLKFREQHZ	100000000


#define	SDSPI_SETAUX	0x0ff
#define	SDSPI_READAUX	0x0bf
#define	SDSPI_CMD		0x040
#define	SDSPI_ACMD		(0x040+55) // CMD55
#define	SDSPI_FIFO_OP	0x0800	// Read only
#define	SDSPI_WRITEOP	0x0c00	// Write to the FIFO
#define	SDSPI_ALTFIFO	0x1000
#define	SDSPI_BUSY		0x4000
#define	SDSPI_ERROR	0x8000
#define	SDSPI_CLEARERR	0x8000
#define	SDSPI_READ_SECTOR	((SDSPI_CMD|SDSPI_CLEARERR|SDSPI_FIFO_OP)+17)
#define	SDSPI_WRITE_SECTOR	((SDSPI_CMD|SDSPI_CLEARERR|SDSPI_WRITEOP)+24)

typedef	struct SDSPI_S {
	unsigned	sd_ctrl, sd_data, sd_fifo[2];
} SDSPI;


#define	SPIO_BTNC	0x01000
#define	SPIO_BTND	0x00800
#define	SPIO_BTNL	0x00400
#define	SPIO_BTNR	0x00200
#define	SPIO_BTNU	0x00100


typedef struct  CONSOLE_S {
	unsigned	u_setup;
	unsigned	u_fifo;
	unsigned	u_rx, u_tx;
} CONSOLE;

#define	_uart_txbusy	((_uart->u_fifo & 0x10000)==0)


//
// The Ethernet MDIO interface
//
#define MDIO_BMCR	0x00
#define MDIO_BMSR	0x01
#define MDIO_PHYIDR1	0x02
#define MDIO_PHYIDR2	0x03
#define MDIO_ANAR	0x04
#define MDIO_ANLPAR	0x05
#define MDIO_ANER	0x06
#define MDIO_ANNPTR	0x07
#define MDIO_ANNPRR	0x08
#define MDIO_GBCR	0x09
#define MDIO_GBSR	0x0a
#define MDIO_MACR	0x0d
#define MDIO_MAADR	0x0e
#define MDIO_GBESR	0x0f
#define MDIO_PHYCR	0x10
#define MDIO_PHYSR	0x11
#define MDIO_INER	0x12
#define MDIO_INSR	0x13
#define MDIO_LDPSR	0x1b
#define MDIO_EPAGSR	0x1e
#define MDIO_PAGSEL	0x1f

#define XMDIO_PC1R	0x00
#define XMDIO_PS1R	0x01
#define XMDIO_EEECR	0x14
#define XMDIO_EEEWER	0x10
// #define XMDIO_EEEAR	0x
// #define XMDIO_EEELPAR	0x18
#define XMDIO_LACR	0x1a
#define XMDIO_LCR	0x1c
// #define XMDIO_ACCR	0x1b

typedef struct ENETMDIO_S {
	unsigned	e_v[32];
} ENETMDIO;



#ifdef	HDMI_OUT_EDID_ACCESS
#define	_BOARD_HAS_HDMI_SRC_EDID
static volatile EDID_SRC *const _edout = ((EDID_SRC *)251658752);
#endif	// HDMI_OUT_EDID_ACCESS
#ifdef	GPSTRK_ACCESS
static volatile GPSTRACKER *const _gps = ((GPSTRACKER *)0x0f000000);
#endif	// GPSTRK_ACCESS
static volatile GPSTB *const _gpstb = ((GPSTB *)0x0f000060);
#ifdef	NETSCOPE_SCOPE
#define	_BOARD_HAS_NETSCOPE
static volatile SCOPE *const _enetscope = ((SCOPE *)0x02000000);
#endif	// NETSCOPE_SCOPE
#define	_BOARD_HAS_ENETB
static volatile unsigned *const _netbrx = ((unsigned *)0x10000000);
static volatile unsigned *const _netbtx = ((unsigned *)(0x10000000 + (0x2000<<1)));
#ifdef	ETHERNET_ACCESS
#define	_BOARD_HAS_ENETP
static volatile ENETPACKET *const _netp = ((ENETPACKET *)0x0b000000);
#endif	// ETHERNET_ACCESS
#ifdef	FLASH_ACCESS
#define	_BOARD_HAS_FLASH
extern int _flash[1];
#endif	// FLASH_ACCESS
#define	_BOARD_HAS_BUILDTIME
#ifdef	MICROPHONE_ACCESS
#define	_BOARD_HAS_WBMIC
static volatile WBMIC *const _wbmic = ((WBMIC *)50331648);
#endif	// MICROPHONE_ACCESS
#ifdef	GPIO_ACCESS
#define	_BOARD_HAS_GPIO
static volatile unsigned *const _gpio = ((unsigned *)201326620);
#endif	// GPIO_ACCESS
#ifdef	MOUSE_ACCESS
#define	_BOARD_HAS_WBMOUSE
static volatile WBMOUSE *const _mouse = ((WBMOUSE *)251658272);
#endif	// MOUSE_ACCESS
#ifdef	HDMI_IN_EDID_ACCESS
#define	_BOARD_HAS_HDMI_IN_EDID
static volatile unsigned *const _edin = ((unsigned *)251658496);
#endif	// HDMI_IN_EDID_ACCESS
#define	_BOARD_HAS_ZIPSCOPE
static volatile WBSCOPE *const _zipscope = ((WBSCOPE *)117440512);
#ifdef	SDSPI_SCOPE
#define	_BOARD_HAS_SDSPI_SCOPE
static volatile WBSCOPE *const _scope_sdcard = ((WBSCOPE *)0x06000000);
#endif	// SDSPI_SCOPE
#ifdef	CFG_ACCESS
#define	_BOARD_HAS_ICAPTETWO
static volatile unsigned *const _icape = ((unsigned *)218103808);
#endif	// CFG_ACCESS
#ifdef	GPSUART_ACCESS
#define	_BOARD_HAS_GPS_UART
static volatile WBUART *const _gpsu = ((WBUART *)(0x08000000));
#endif	// GPSUART_ACCESS
#ifdef	BUSPIC_ACCESS
#define	_BOARD_HAS_BUSPIC
static volatile unsigned *const _buspic = ((unsigned *)0x0c000008);
#endif	// BUSPIC_ACCESS
#ifdef	HDMIIN_ACCESS
#define	_BOARD_HAS_HDMI_IN
static volatile HDMI_IN *const _hin = ((HDMI_IN *)251658368);
#endif	// HDMIIN_ACCESS
#define	_BOARD_HAS_SUBSECONDS
static volatile unsigned *const _subseconds = ((unsigned *)0x0c000034);
#ifdef	RTC_ACCESS
#define	_BOARD_HAS_RTC
static volatile RTCLIGHT *const _rtc = ((RTCLIGHT *)0x0f000040);
#endif	// RTC_ACCESS
#ifdef	BKRAM_ACCESS
#define	_BOARD_HAS_BKRAM
extern char	_bkram[0x00100000];
#endif	// BKRAM_ACCESS
#define	_BOARD_HAS_VERSION
#ifdef	FLASHCFG_ACCESS
#define	_BOARD_HAS_FLASHCFG
static volatile unsigned * const _flashcfg = ((unsigned *)(0x01000000));
#endif	// FLASHCFG_ACCESS
#define	_BOARD_HAS_BUSERR
static volatile unsigned *const _buserr = ((unsigned *)201326596);
#ifdef	SDRAM_ACCESS
#define	_BOARD_HAS_SDRAM
extern char	_sdram[0x20000000];
#endif	// SDRAM_ACCESS
#ifdef	SDSPI_ACCESS
#define	_BOARD_HAS_SDSPI
static volatile SDSPI *const _sdcard = ((SDSPI *)0x09000000);
#endif	// SDSPI_ACCESS
#ifdef	SPIO_ACCESS
#define	_BOARD_HAS_SPIO
static volatile unsigned *const _spio = ((unsigned *)201326640);
#endif	// SPIO_ACCESS
#ifdef	PWRCOUNT_ACCESS
static volatile unsigned *const _pwrcount = ((unsigned *)0x0c000028);
#endif	// PWRCOUNT_ACCESS
#ifdef	RTCDATE_ACCESS
#define	_BOARD_HAS_RTCDATE
static volatile unsigned *const _rtcdate = ((unsigned *)201326636);
#endif	// RTCDATE_ACCESS
#ifdef	BUSCONSOLE_ACCESS
#define	_BOARD_HAS_BUSCONSOLE
static volatile CONSOLE *const _uart = ((CONSOLE *)0x0a000000);
#endif	// BUSCONSOLE_ACCESS
#ifdef	NETCTRL_ACCESS
#define	_BOARD_HAS_NETMDIO
static volatile ENETMDIO *const _mdio = ((ENETMDIO *)234881024);
#endif	// NETCTRL_ACCESS
//
// Interrupt assignments (3 PICs)
//
// PIC: syspic
#define	SYSPIC_DMAC	SYSPIC(0)
#define	SYSPIC_JIFFIES	SYSPIC(1)
#define	SYSPIC_TMC	SYSPIC(2)
#define	SYSPIC_TMB	SYSPIC(3)
#define	SYSPIC_TMA	SYSPIC(4)
#define	SYSPIC_ALT	SYSPIC(5)
#define	SYSPIC_BUS	SYSPIC(6)
#define	SYSPIC_PPS	SYSPIC(7)
#define	SYSPIC_NETTX	SYSPIC(8)
#define	SYSPIC_NETRX	SYSPIC(9)
#define	SYSPIC_MIC	SYSPIC(10)
#define	SYSPIC_MOUSE	SYSPIC(11)
#define	SYSPIC_SDCARD	SYSPIC(12)
#define	SYSPIC_UARTTXF	SYSPIC(13)
#define	SYSPIC_UARTRXF	SYSPIC(14)
// PIC: altpic
#define	ALTPIC_UIC	ALTPIC(0)
#define	ALTPIC_UOC	ALTPIC(1)
#define	ALTPIC_UPC	ALTPIC(2)
#define	ALTPIC_UTC	ALTPIC(3)
#define	ALTPIC_MIC	ALTPIC(4)
#define	ALTPIC_MOC	ALTPIC(5)
#define	ALTPIC_MPC	ALTPIC(6)
#define	ALTPIC_MTC	ALTPIC(7)
#define	ALTPIC_EDID	ALTPIC(8)
#define	ALTPIC_GPIO	ALTPIC(9)
#define	ALTPIC_GPSRX	ALTPIC(10)
#define	ALTPIC_GPSTX	ALTPIC(11)
#define	ALTPIC_GPSRXF	ALTPIC(12)
#define	ALTPIC_GPSTXF	ALTPIC(13)
#define	ALTPIC_RTC	ALTPIC(14)
// PIC: buspic
#define	BUSPIC_SCOPE	BUSPIC(0)
#define	BUSPIC_ENETSCOPE	BUSPIC(1)
#define	BUSPIC_MOUSE	BUSPIC(2)
#define	BUSPIC_ZIPSCOPE	BUSPIC(3)
#define	BUSPIC_HINSCOPE	BUSPIC(4)
#define	BUSPIC_SDCARD	BUSPIC(5)
#define	BUSPIC_SPIO	BUSPIC(6)
#define	SYSINT_PPS	SYSINT(7)


#define	SYSINT_GPSRXF	ALTINT(@$(INT.GPSRXF.syspic.ID))
#define	SYSINT_GPSTXF	ALTINT(13)
#define	SYSINT_GPSRX	ALTINT(10)
#define	SYSINT_GPSTX	ALTINT(11)


#endif	// BOARD_H
