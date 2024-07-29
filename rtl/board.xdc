### This file is a general .xdc for the Nexys Video Rev. A
### To use it in a project:
### - uncomment the lines corresponding to used pins
### - rename the used ports (in each line, after get_ports) according to the top level signal names in the project


## Clock Signal
## {{{
set_property -dict {PACKAGE_PIN R4 IOSTANDARD LVCMOS33} [get_ports i_clk]
create_clock -period 10.000 -name INCLK -waveform {0.000 5.000} -add [get_ports i_clk]
## }}}


## FMC Transceiver clocks (Must be set to value provided by Mezzanine card, currently set to 156.25 MHz)
## {{{
## Note: This clock is attached to a MGTREFCLK pin
#set_property -dict { PACKAGE_PIN E6 } [get_ports { GTP_CLK_N }];
#set_property -dict { PACKAGE_PIN F6 } [get_ports { GTP_CLK_P }];
#create_clock -add -name gtpclk0_pin -period 6.400 -waveform {0 3.200} [get_ports {GTP_CLK_P}];
#set_property -dict { PACKAGE_PIN E10 } [get_ports { FMC_MGT_CLK_N }];
#set_property -dict { PACKAGE_PIN F10 } [get_ports { FMC_MGT_CLK_P }];
#create_clock -add -name mgtclk1_pin -period 6.400 -waveform {0 3.200} [get_ports {FMC_MGT_CLK_P}];
## }}}


## LEDs
## {{{
## The correct voltage for the LEDs is not really given in either the LED
## circuit or the reference manual.  However, according to the schematic they
## are connected to the 2.5V bank.  Hence they are declared LVCMOS25 here.
set_property -dict {PACKAGE_PIN T14 IOSTANDARD LVCMOS25} [get_ports {o_led[0]}]
set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS25} [get_ports {o_led[1]}]
set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS25} [get_ports {o_led[2]}]
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS25} [get_ports {o_led[3]}]
set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS25} [get_ports {o_led[4]}]
set_property -dict {PACKAGE_PIN W16 IOSTANDARD LVCMOS25} [get_ports {o_led[5]}]
set_property -dict {PACKAGE_PIN W15 IOSTANDARD LVCMOS25} [get_ports {o_led[6]}]
set_property -dict {PACKAGE_PIN Y13 IOSTANDARD LVCMOS25} [get_ports {o_led[7]}]
## }}}

## Buttons
## {{{
## The correct voltage for the buttons is VADJ.  If you adjust VADJ, adjust the
## button voltages.
set_property -dict {PACKAGE_PIN B22 IOSTANDARD LVCMOS33} [get_ports i_btnc]
set_property -dict {PACKAGE_PIN D22 IOSTANDARD LVCMOS33} [get_ports i_btnd]
set_property -dict {PACKAGE_PIN C22 IOSTANDARD LVCMOS33} [get_ports i_btnl]
set_property -dict {PACKAGE_PIN D14 IOSTANDARD LVCMOS33} [get_ports i_btnr]
set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports i_btnu]
#set_property -dict {PACKAGE_PIN G4  IOSTANDARD LVCMOS33} [get_ports i_cpu_resetn]
## }}}

## Switches
## {{{
## The correct voltage for the switches is VADJ.  If you adjust VADJ, adjust
## the switch voltage.
set_property -dict {PACKAGE_PIN E22 IOSTANDARD LVCMOS33} [get_ports {i_sw[0]}]
set_property -dict {PACKAGE_PIN F21 IOSTANDARD LVCMOS33} [get_ports {i_sw[1]}]
set_property -dict {PACKAGE_PIN G21 IOSTANDARD LVCMOS33} [get_ports {i_sw[2]}]
set_property -dict {PACKAGE_PIN G22 IOSTANDARD LVCMOS33} [get_ports {i_sw[3]}]
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {i_sw[4]}]
set_property -dict {PACKAGE_PIN J16 IOSTANDARD LVCMOS33} [get_ports {i_sw[5]}]
set_property -dict {PACKAGE_PIN K13 IOSTANDARD LVCMOS33} [get_ports {i_sw[6]}]
set_property -dict {PACKAGE_PIN M17 IOSTANDARD LVCMOS33} [get_ports {i_sw[7]}]
## }}}

## OLED Display
## {{{
#set_property -dict { PACKAGE_PIN W22   IOSTANDARD LVCMOS33 } [get_ports { o_oled_dcn      }]; #IO_L7N_T1_D10_14 Sch=oled_dc SPI select port
#set_property -dict { PACKAGE_PIN U21   IOSTANDARD LVCMOS33 } [get_ports { o_oled_reset_n  }]; #IO_L4N_T0_D05_14 Sch=oled_res RESET
#set_property -dict { PACKAGE_PIN W21   IOSTANDARD LVCMOS33 } [get_ports { o_oled_sck      }]; #IO_L7P_T1_D09_14 Sch=oled_sclk SPI Clk port
#set_property -dict { PACKAGE_PIN Y22   IOSTANDARD LVCMOS33 } [get_ports { o_oled_mosi     }]; #IO_L9N_T1_DQS_D13_14 Sch=oled_sdin Data port
#set_property -dict { PACKAGE_PIN P20   IOSTANDARD LVCMOS33 } [get_ports { o_oled_panel_en }]; #IO_0_14 Sch=oled_vbat VBAT
#set_property -dict { PACKAGE_PIN V22   IOSTANDARD LVCMOS33 } [get_ports { o_oled_logic_en }]; #IO_L3N_T0_DQS_EMCCLK_14 Sch=oled_vdd VDD
## }}}


## HDMI in
## {{{
set_property -dict { PACKAGE_PIN AA5   IOSTANDARD LVCMOS33    } [get_ports   io_hdmirx_cec  ]
set_property -dict { PACKAGE_PIN W4    IOSTANDARD TMDS_33     } [get_ports   i_hdmirx_clk_n  ]
set_property -dict { PACKAGE_PIN V4    IOSTANDARD TMDS_33     } [get_ports   i_hdmirx_clk_p  ]
set_property -dict { PACKAGE_PIN AB12  IOSTANDARD LVCMOS25    } [get_ports   o_hdmirx_hpa    ]
set_property -dict { PACKAGE_PIN Y4    IOSTANDARD LVCMOS33    } [get_ports   io_hdmirx_scl   ]
set_property -dict { PACKAGE_PIN AB5   IOSTANDARD LVCMOS33    } [get_ports   io_hdmirx_sda   ]
set_property -dict { PACKAGE_PIN R3    IOSTANDARD LVCMOS33    } [get_ports   o_hdmirx_txen   ]
set_property -dict { PACKAGE_PIN AA3   IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_n[0] } ]; #IO_L9N_T1_DQS_34 Sch=hdmi_rx_n[0]
set_property -dict { PACKAGE_PIN Y3    IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_p[0] } ]; #IO_L9P_T1_DQS_34 Sch=hdmi_rx_p[0]
set_property -dict { PACKAGE_PIN Y2    IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_n[1] } ]; #IO_L4N_T0_34 Sch=hdmi_rx_n[1]
set_property -dict { PACKAGE_PIN W2    IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_p[1] } ]; #IO_L4P_T0_34 Sch=hdmi_rx_p[1]
set_property -dict { PACKAGE_PIN V2    IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_n[2] } ]; #IO_L2N_T0_34 Sch=hdmi_rx_n[2]
set_property -dict { PACKAGE_PIN U2    IOSTANDARD TMDS_33     } [get_ports { i_hdmirx_p[2] } ]; #IO_L2P_T0_34 Sch=hdmi_rx_p[2]
## }}}

## HDMI out
## {{{
set_property -dict { PACKAGE_PIN AA4   IOSTANDARD LVCMOS33    } [get_ports   io_hdmitx_cec  ]
set_property -dict { PACKAGE_PIN U1    IOSTANDARD TMDS_33     } [get_ports   o_hdmitx_clk_n ]
set_property -dict { PACKAGE_PIN T1    IOSTANDARD TMDS_33     } [get_ports   o_hdmitx_clk_p ]
set_property -dict { PACKAGE_PIN AB13  IOSTANDARD LVCMOS25    } [get_ports   i_hdmitx_hpd_n ]
set_property -dict { PACKAGE_PIN U3    IOSTANDARD LVCMOS33    } [get_ports { io_hdmitx_scl }]; #IO_L6P_T0_34 Sch=hdmi_tx_rscl
set_property -dict { PACKAGE_PIN V3    IOSTANDARD LVCMOS33    } [get_ports { io_hdmitx_sda }]; #IO_L6N_T0_VREF_34 Sch=hdmi_tx_rsda
set_property -dict { PACKAGE_PIN Y1    IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_n[0] }]; #IO_L5N_T0_34 Sch=hdmi_tx_n[0]
set_property -dict { PACKAGE_PIN W1    IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_p[0] }]; #IO_L5P_T0_34 Sch=hdmi_tx_p[0]
set_property -dict { PACKAGE_PIN AB1   IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_n[1] }]; #IO_L7N_T1_34 Sch=hdmi_tx_n[1]
set_property -dict { PACKAGE_PIN AA1   IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_p[1] }]; #IO_L7P_T1_34 Sch=hdmi_tx_p[1]
set_property -dict { PACKAGE_PIN AB2   IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_n[2] }]; #IO_L8N_T1_34 Sch=hdmi_tx_n[2]
set_property -dict { PACKAGE_PIN AB3   IOSTANDARD TMDS_33     } [get_ports { o_hdmitx_p[2] }]; #IO_L8P_T1_34 Sch=hdmi_tx_p[2]
## }}}

## Display Port
## {{{
#set_property -dict { PACKAGE_PIN AB10  IOSTANDARD LVDS     } [get_ports { dp_tx_aux_n }]; #IO_L8N_T1_13 Sch=dp_tx_aux_n
#set_property -dict { PACKAGE_PIN AA11  IOSTANDARD LVDS     } [get_ports { dp_tx_aux_n }]; #IO_L9N_T1_DQS_13 Sch=dp_tx_aux_n
#set_property -dict { PACKAGE_PIN AA9   IOSTANDARD LVDS     } [get_ports { dp_tx_aux_p }]; #IO_L8P_T1_13 Sch=dp_tx_aux_p
#set_property -dict { PACKAGE_PIN AA10  IOSTANDARD LVDS     } [get_ports { dp_tx_aux_p }]; #IO_L9P_T1_DQS_13 Sch=dp_tx_aux_p
#set_property -dict { PACKAGE_PIN N15   IOSTANDARD LVCMOS33 } [get_ports { dp_tx_hpd }]; #IO_25_14 Sch=dp_tx_hpd
## }}}


## Audio Codec
## {{{
#set_property -dict { PACKAGE_PIN T4    IOSTANDARD LVCMOS33 } [get_ports { i_i2s_adc }]; #IO_L13N_T2_MRCC_34 Sch=ac_adc_sdata
#set_property -dict { PACKAGE_PIN T5    IOSTANDARD LVCMOS33 } [get_ports { o_i2s_bclk }]; #IO_L14P_T2_SRCC_34 Sch=ac_bclk
#set_property -dict { PACKAGE_PIN W6    IOSTANDARD LVCMOS33 } [get_ports { o_i2s_dac }]; #IO_L15P_T2_DQS_34 Sch=ac_dac_sdata
#set_property -dict { PACKAGE_PIN U5    IOSTANDARD LVCMOS33 } [get_ports { o_i2s_lrclk }]; #IO_L14N_T2_SRCC_34 Sch=ac_lrclk
#set_property -dict { PACKAGE_PIN U6    IOSTANDARD LVCMOS33 } [get_ports { o_i2s_mclk }]; #IO_L16P_T2_34 Sch=ac_mclk

## I2C Audio configuration
set_property -dict { PACKAGE_PIN V5	IOSTANDARD LVCMOS33 } [get_ports { io_sda }]; #IO_L16N_T2_34 Sch=sda
set_property -dict { PACKAGE_PIN W5	IOSTANDARD LVCMOS33 } [get_ports { io_scl }]; #IO_L15N_T2_DQS_34 Sch=scl
## }}}

## Pmod header JA -- We'll use the bottom for GPS
## {{{
#set_property -dict { PACKAGE_PIN AB22  IOSTANDARD LVCMOS33 } [get_ports { ja[0] }]; #IO_L10N_T1_D15_14 Sch=ja[1]
#set_property -dict { PACKAGE_PIN AB21  IOSTANDARD LVCMOS33 } [get_ports { ja[1] }]; #IO_L10P_T1_D14_14 Sch=ja[2]
#set_property -dict { PACKAGE_PIN AB20  IOSTANDARD LVCMOS33 } [get_ports { ja[2] }]; #IO_L15N_T2_DQS_DOUT_CSO_B_14 Sch=ja[3]
#set_property -dict { PACKAGE_PIN AB18  IOSTANDARD LVCMOS33 } [get_ports { ja[3] }]; #IO_L17N_T2_A13_D29_14 Sch=ja[4]
set_property -dict {PACKAGE_PIN Y21  IOSTANDARD LVCMOS33} [get_ports i_gps_3df]
#set_property -dict {PACKAGE_PIN AA21 IOSTANDARD LVCMOS33} [get_ports o_gpsu_tx]
#set_property -dict {PACKAGE_PIN AA20 IOSTANDARD LVCMOS33} [get_ports i_gpsu_rx]
#set_property -dict {PACKAGE_PIN AA18 IOSTANDARD LVCMOS33} [get_ports i_gps_pps]
## }}}


## Pmod header JB --- Reserved for the Differential PMod Challenge
## {{{
#set_property -dict { PACKAGE_PIN V9    IOSTANDARD LVCMOS33 } [get_ports { io_genclk }]; #IO_L19P_T3_34 Sch=jb_p[2]
#set_property -dict { PACKAGE_PIN V9    IOSTANDARD LVCMOS33 } [get_ports { jb[0] }]; #IO_L21P_T3_DQS_34 Sch=jb_p[1]
#set_property -dict { PACKAGE_PIN V8    IOSTANDARD LVCMOS33 } [get_ports { jb[1] }]; #IO_L21N_T3_DQS_34 Sch=jb_n[1]
#set_property -dict { PACKAGE_PIN V7    IOSTANDARD LVCMOS33 } [get_ports { jb[2] }]; #IO_L19P_T3_34 Sch=jb_p[2]
#set_property -dict { PACKAGE_PIN W7    IOSTANDARD LVCMOS33 } [get_ports { jb[3] }]; #IO_L19N_T3_VREF_34 Sch=jb_n[2]
#set_property -dict { PACKAGE_PIN W9    IOSTANDARD LVCMOS33 } [get_ports { jb[4] }]; #IO_L24P_T3_34 Sch=jb_p[3]
#set_property -dict { PACKAGE_PIN Y9    IOSTANDARD LVCMOS33 } [get_ports { jb[5] }]; #IO_L24N_T3_34 Sch=jb_n[3]
#set_property -dict { PACKAGE_PIN Y8    IOSTANDARD LVCMOS33 } [get_ports { jb[6] }]; #IO_L23P_T3_34 Sch=jb_p[4]
#set_property -dict { PACKAGE_PIN Y7    IOSTANDARD LVCMOS33 } [get_ports { jb[7] }]; #IO_L23N_T3_34 Sch=jb_n[4]
## }}}


## Pmod header JC  -- We'll use the bottom for the PModMIC
## {{{
#set_property -dict { PACKAGE_PIN Y6    IOSTANDARD LVCMOS33 } [get_ports { jc[0] }]; #IO_L18P_T2_34 Sch=jc_p[1]
#set_property -dict { PACKAGE_PIN AA6   IOSTANDARD LVCMOS33 } [get_ports { jc[1] }]; #IO_L18N_T2_34 Sch=jc_n[1]
#set_property -dict { PACKAGE_PIN AA8   IOSTANDARD LVCMOS33 } [get_ports { jc[2] }]; #IO_L22P_T3_34 Sch=jc_p[2]
#set_property -dict { PACKAGE_PIN AB8   IOSTANDARD LVCMOS33 } [get_ports { jc[3] }]; #IO_L22N_T3_34 Sch=jc_n[2]
#set_property -dict { PACKAGE_PIN R6    IOSTANDARD LVCMOS33 } [get_ports { o_mic_csn }]; #IO_L17P_T2_34 Sch=jc_p[3]
## set_property -dict { PACKAGE_PIN T6    IOSTANDARD LVCMOS33 } [get_ports { jc[5] }]; #IO_L17N_T2_34 Sch=jc_n[3]
#set_property -dict { PACKAGE_PIN AB7   IOSTANDARD LVCMOS33 } [get_ports { i_mic_din }]; #IO_L20P_T3_34 Sch=jc_p[4]
#set_property -dict { PACKAGE_PIN AB6   IOSTANDARD LVCMOS33 } [get_ports { o_mic_sck }]; #IO_L20N_T3_34 Sch=jc_n[4]
## }}}


## XADC Header
## {{{
#set_property -dict { PACKAGE_PIN J14   IOSTANDARD LVCMOS33 } [get_ports { xa_p[0] }]; #IO_L3P_T0_DQS_AD1P_15 Sch=xa_p[1]
#set_property -dict { PACKAGE_PIN H14   IOSTANDARD LVCMOS33 } [get_ports { xa_n[0] }]; #IO_L3N_T0_DQS_AD1N_15 Sch=xa_n[1]
#set_property -dict { PACKAGE_PIN H13   IOSTANDARD LVCMOS33 } [get_ports { xa_p[1] }]; #IO_L1P_T0_AD0P_15 Sch=xa_p[2]
#set_property -dict { PACKAGE_PIN G13   IOSTANDARD LVCMOS33 } [get_ports { xa_n[1] }]; #IO_L1N_T0_AD0N_15 Sch=xa_n[2]
#set_property -dict { PACKAGE_PIN G15   IOSTANDARD LVCMOS33 } [get_ports { xa_p[2] }]; #IO_L2P_T0_AD8P_15 Sch=xa_p[3]
#set_property -dict { PACKAGE_PIN G16   IOSTANDARD LVCMOS33 } [get_ports { xa_n[2] }]; #IO_L2N_T0_AD8N_15 Sch=xa_n[3]
#set_property -dict { PACKAGE_PIN J15   IOSTANDARD LVCMOS33 } [get_ports { xa_p[3] }]; #IO_L5P_T0_AD9P_15 Sch=xa_p[4]
#set_property -dict { PACKAGE_PIN H15   IOSTANDARD LVCMOS33 } [get_ports { xa_n[3] }]; #IO_L5N_T0_AD9N_15 Sch=xa_n[4]
## }}}


## UART
## {{{
set_property -dict {PACKAGE_PIN AA19 IOSTANDARD LVCMOS33 } [get_ports o_wbu_uart_tx ]
set_property -dict {PACKAGE_PIN V18  IOSTANDARD LVCMOS33 } [get_ports i_wbu_uart_rx ]
## }}}


## Ethernet
## {{{
#set_property -dict { PACKAGE_PIN Y14   IOSTANDARD LVCMOS25 } [get_ports { eth_int_b }]; #IO_L6N_T0_VREF_13 Sch=eth_int_b
set_property -dict {PACKAGE_PIN AA16 IOSTANDARD LVCMOS25} [get_ports o_eth_mdclk]
set_property -dict {PACKAGE_PIN Y16 IOSTANDARD LVCMOS25} [get_ports io_eth_mdio]
#set_property -dict { PACKAGE_PIN W14   IOSTANDARD LVCMOS25 } [get_ports { eth_pme_b }]; #IO_L6P_T0_13 Sch=eth_pme_b
set_property -dict { PACKAGE_PIN U7    IOSTANDARD LVCMOS33 } [get_ports { o_net_reset_n }]; #IO_25_34 Sch=eth_rst_b
set_property -dict { PACKAGE_PIN V13   IOSTANDARD LVCMOS25 } [get_ports { i_net_rx_clk }]; #IO_L13P_T2_MRCC_13 Sch=eth_rxck
set_property -dict { PACKAGE_PIN W10   IOSTANDARD LVCMOS25 } [get_ports { i_net_rx_ctl }]; #IO_L10N_T1_13 Sch=eth_rxctl
set_property -dict { PACKAGE_PIN AB16  IOSTANDARD LVCMOS25 } [get_ports { i_net_rxd[0] }]; #IO_L2P_T0_13 Sch=eth_rxd[0]
set_property -dict { PACKAGE_PIN AA15  IOSTANDARD LVCMOS25 } [get_ports { i_net_rxd[1] }]; #IO_L4P_T0_13 Sch=eth_rxd[1]
set_property -dict { PACKAGE_PIN AB15  IOSTANDARD LVCMOS25 } [get_ports { i_net_rxd[2] }]; #IO_L4N_T0_13 Sch=eth_rxd[2]
set_property -dict { PACKAGE_PIN AB11  IOSTANDARD LVCMOS25 } [get_ports { i_net_rxd[3] }]; #IO_L7P_T1_13 Sch=eth_rxd[3]
set_property -dict { PACKAGE_PIN AA14  IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_tx_clk }]; #IO_L5N_T0_13 Sch=eth_txck
set_property -dict { PACKAGE_PIN V10   IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_tx_ctl }]; #IO_L10P_T1_13 Sch=eth_txctl
set_property -dict { PACKAGE_PIN Y12   IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_txd[0] }]; #IO_L11N_T1_SRCC_13 Sch=eth_txd[0]
set_property -dict { PACKAGE_PIN W12   IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_txd[1] }]; #IO_L12N_T1_MRCC_13 Sch=eth_txd[1]
set_property -dict { PACKAGE_PIN W11   IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_txd[2] }]; #IO_L12P_T1_MRCC_13 Sch=eth_txd[2]
set_property -dict { PACKAGE_PIN Y11   IOSTANDARD LVCMOS25 SLEW FAST } [get_ports { o_net_txd[3] }]; #IO_L11P_T1_SRCC_13 Sch=eth_txd[3]
## }}}

## Fan PWM
set_property -dict { PACKAGE_PIN U15   IOSTANDARD LVCMOS25 } [get_ports { o_unused_fan_pwm }]; #IO_L14P_T2_SRCC_13 Sch=fan_pwm


## DPTI/DSPI
## {{{
#set_property -dict { PACKAGE_PIN Y18   IOSTANDARD LVCMOS33 } [get_ports { prog_clko  }]; #IO_L13P_T2_MRCC_14 Sch=prog_clko
#set_property -dict { PACKAGE_PIN U20   IOSTANDARD LVCMOS33 } [get_ports { prog_d[0]  }]; #IO_L11P_T1_SRCC_14 Sch=prog_d0/sck
#set_property -dict { PACKAGE_PIN P14   IOSTANDARD LVCMOS33 } [get_ports { prog_d[1]  }]; #IO_L19P_T3_A10_D26_14 Sch=prog_d1/mosi
#set_property -dict { PACKAGE_PIN P15   IOSTANDARD LVCMOS33 } [get_ports { prog_d[2]  }]; #IO_L22P_T3_A05_D21_14 Sch=prog_d2/miso
#set_property -dict { PACKAGE_PIN U17   IOSTANDARD LVCMOS33 } [get_ports { prog_d[3]  }]; #IO_L18P_T2_A12_D28_14 Sch=prog_d3/ss
#set_property -dict { PACKAGE_PIN R17   IOSTANDARD LVCMOS33 } [get_ports { prog_d[4]  }]; #IO_L24N_T3_A00_D16_14 Sch=prog_d[4]
#set_property -dict { PACKAGE_PIN P16   IOSTANDARD LVCMOS33 } [get_ports { prog_d[5]  }]; #IO_L24P_T3_A01_D17_14 Sch=prog_d[5]
#set_property -dict { PACKAGE_PIN R18   IOSTANDARD LVCMOS33 } [get_ports { prog_d[6]  }]; #IO_L20P_T3_A08_D24_14 Sch=prog_d[6]
#set_property -dict { PACKAGE_PIN N14   IOSTANDARD LVCMOS33 } [get_ports { prog_d[7]  }]; #IO_L23N_T3_A02_D18_14 Sch=prog_d[7]
#set_property -dict { PACKAGE_PIN V17   IOSTANDARD LVCMOS33 } [get_ports { prog_oen   }]; #IO_L16P_T2_CSI_B_14 Sch=prog_oen
#set_property -dict { PACKAGE_PIN P19   IOSTANDARD LVCMOS33 } [get_ports { prog_rdn   }]; #IO_L5P_T0_D06_14 Sch=prog_rdn
#set_property -dict { PACKAGE_PIN N17   IOSTANDARD LVCMOS33 } [get_ports { prog_rxen  }]; #IO_L21P_T3_DQS_14 Sch=prog_rxen
#set_property -dict { PACKAGE_PIN P17   IOSTANDARD LVCMOS33 } [get_ports { prog_siwun }]; #IO_L21N_T3_DQS_A06_D22_14 Sch=prog_siwun
#set_property -dict { PACKAGE_PIN R14   IOSTANDARD LVCMOS33 } [get_ports { prog_spien }]; #IO_L19N_T3_A09_D25_VREF_14 Sch=prog_spien
#set_property -dict { PACKAGE_PIN Y19   IOSTANDARD LVCMOS33 } [get_ports { prog_txen  }]; #IO_L13N_T2_MRCC_14 Sch=prog_txen
#set_property -dict { PACKAGE_PIN R19   IOSTANDARD LVCMOS33 } [get_ports { prog_wrn   }]; #IO_L5N_T0_D07_14 Sch=prog_wrn
## }}}


## PS2 HID port
## {{{
#set_property -dict {PACKAGE_PIN W17 IOSTANDARD LVCMOS33} [get_ports io_ps2_clk]
#set_property -dict {PACKAGE_PIN N13 IOSTANDARD LVCMOS33} [get_ports io_ps2_data]
## }}}


## QSPI
## {{{
set_property -dict {PACKAGE_PIN T19 IOSTANDARD LVCMOS33} [get_ports o_qspi_cs_n]
set_property -dict {PACKAGE_PIN P22 IOSTANDARD LVCMOS33} [get_ports {io_qspi_dat[0]}]
set_property -dict {PACKAGE_PIN R22 IOSTANDARD LVCMOS33} [get_ports {io_qspi_dat[1]}]
set_property -dict {PACKAGE_PIN P21 IOSTANDARD LVCMOS33} [get_ports {io_qspi_dat[2]}]
set_property -dict {PACKAGE_PIN R21 IOSTANDARD LVCMOS33} [get_ports {io_qspi_dat[3]}]
## }}}


## SD card
## {{{
set_property -dict { PACKAGE_PIN W19   IOSTANDARD LVCMOS33 } [get_ports { o_sd_clk }]; #IO_L12P_T1_MRCC_14 Sch=sd_cclk
set_property -dict {PACKAGE_PIN T18 IOSTANDARD LVCMOS33} [get_ports i_sd_cd_n]
set_property -dict { PACKAGE_PIN W20   IOSTANDARD LVCMOS33 } [get_ports { io_sd_cmd }]; #IO_L12N_T1_MRCC_14 Sch=sd_cmd
set_property -dict { PACKAGE_PIN V19   IOSTANDARD LVCMOS33 } [get_ports { io_sd_dat[0] }]; #IO_L14N_T2_SRCC_14 Sch=sd_d[0]
set_property -dict { PACKAGE_PIN T21   IOSTANDARD LVCMOS33 } [get_ports { io_sd_dat[1] }]; #IO_L4P_T0_D04_14 Sch=sd_d[1]
set_property -dict { PACKAGE_PIN T20   IOSTANDARD LVCMOS33 } [get_ports { io_sd_dat[2] }]; #IO_L6N_T0_D08_VREF_14 Sch=sd_d[2]
set_property -dict { PACKAGE_PIN U18   IOSTANDARD LVCMOS33 } [get_ports { io_sd_dat[3] }]; #IO_L18N_T2_A11_D27_14 Sch=sd_d[3]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports o_sd_reset]
## }}}

## Voltage Adjust -- *MUST* be set to use FMC
## {{{
set_property -dict { PACKAGE_PIN AA13  IOSTANDARD LVCMOS25 } [get_ports { o_vadj[0] }]; #IO_L3P_T0_DQS_13 Sch=set_vadj[0]
set_property -dict { PACKAGE_PIN AB17  IOSTANDARD LVCMOS25 } [get_ports { o_vadj[1] }]; #IO_L2N_T0_13 Sch=set_vadj[1]
set_property -dict { PACKAGE_PIN V14   IOSTANDARD LVCMOS25 } [get_ports { o_vadj_en }]; #IO_L13N_T2_MRCC_13 Sch=vadj_en
## }}}

## FMC
## {{{
#set_property -dict { PACKAGE_PIN H19   IOSTANDARD LVCMOS12 } [get_ports { fmc_clk0_m2c_n }]; #IO_L12N_T1_MRCC_15 Sch=fmc_clk0_m2c_n
#set_property -dict { PACKAGE_PIN J19   IOSTANDARD LVCMOS12 } [get_ports { fmc_clk0_m2c_p }]; #IO_L12P_T1_MRCC_15 Sch=fmc_clk0_m2c_p
#set_property -dict { PACKAGE_PIN C19   IOSTANDARD LVCMOS12 } [get_ports { fmc_clk1_m2c_n }]; #IO_L13N_T2_MRCC_16 Sch=fmc_clk1_m2c_n
#set_property -dict { PACKAGE_PIN C18   IOSTANDARD LVCMOS12 } [get_ports { fmc_clk1_m2c_p }]; #IO_L13P_T2_MRCC_16 Sch=fmc_clk1_m2c_p
#set_property -dict { PACKAGE_PIN K19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la00_cc_n }]; #IO_L13N_T2_MRCC_15 Sch=fmc_la00_cc_n
#set_property -dict { PACKAGE_PIN K18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la00_cc_p }]; #IO_L13P_T2_MRCC_15 Sch=fmc_la00_cc_p
#set_property -dict { PACKAGE_PIN J21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la01_cc_n }]; #IO_L11N_T1_SRCC_15 Sch=fmc_la01_cc_n
#set_property -dict { PACKAGE_PIN J20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la01_cc_p }]; #IO_L11P_T1_SRCC_15 Sch=fmc_la01_cc_p
#set_property -dict { PACKAGE_PIN L18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[02] }]; #IO_L16N_T2_A27_15 Sch=fmc_la_n[02]
#set_property -dict { PACKAGE_PIN M18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[02] }]; #IO_L16P_T2_A28_15 Sch=fmc_la_p[02]
#set_property -dict { PACKAGE_PIN N19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[03] }]; #IO_L17N_T2_A25_15 Sch=fmc_la_n[03]
#set_property -dict { PACKAGE_PIN N18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[03] }]; #IO_L17P_T2_A26_15 Sch=fmc_la_p[03]
#set_property -dict { PACKAGE_PIN M20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[04] }]; #IO_L18N_T2_A23_15 Sch=fmc_la_n[04]
#set_property -dict { PACKAGE_PIN N20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[04] }]; #IO_L18P_T2_A24_15 Sch=fmc_la_p[04]
#set_property -dict { PACKAGE_PIN L21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[05] }]; #IO_L10N_T1_AD11N_15 Sch=fmc_la_n[05]
#set_property -dict { PACKAGE_PIN M21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[05] }]; #IO_L10P_T1_AD11P_15 Sch=fmc_la_p[05]
#set_property -dict { PACKAGE_PIN M22   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[06] }]; #IO_L15N_T2_DQS_ADV_B_15 Sch=fmc_la_n[06]
#set_property -dict { PACKAGE_PIN N22   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[06] }]; #IO_L15P_T2_DQS_15 Sch=fmc_la_p[06]
#set_property -dict { PACKAGE_PIN L13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[07] }]; #IO_L20N_T3_A19_15 Sch=fmc_la_n[07]
#set_property -dict { PACKAGE_PIN M13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[07] }]; #IO_L20P_T3_A20_15 Sch=fmc_la_p[07]
#set_property -dict { PACKAGE_PIN M16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[08] }]; #IO_L24N_T3_RS0_15 Sch=fmc_la_n[08]
#set_property -dict { PACKAGE_PIN M15   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[08] }]; #IO_L24P_T3_RS1_15 Sch=fmc_la_p[08]
#set_property -dict { PACKAGE_PIN G20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[09] }]; #IO_L8N_T1_AD10N_15 Sch=fmc_la_n[09]
#set_property -dict { PACKAGE_PIN H20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[09] }]; #IO_L8P_T1_AD10P_15 Sch=fmc_la_p[09]
#set_property -dict { PACKAGE_PIN K22   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[10] }]; #IO_L9N_T1_DQS_AD3N_15 Sch=fmc_la_n[10]
#set_property -dict { PACKAGE_PIN K21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[10] }]; #IO_L9P_T1_DQS_AD3P_15 Sch=fmc_la_p[10]
#set_property -dict { PACKAGE_PIN L15   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[11] }]; #IO_L22N_T3_A16_15 Sch=fmc_la_n[11]
#set_property -dict { PACKAGE_PIN L14   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[11] }]; #IO_L22P_T3_A17_15 Sch=fmc_la_p[11]
#set_property -dict { PACKAGE_PIN L20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[12] }]; #IO_L14N_T2_SRCC_15 Sch=fmc_la_n[12]
#set_property -dict { PACKAGE_PIN L19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[12] }]; #IO_L14P_T2_SRCC_15 Sch=fmc_la_p[12]
#set_property -dict { PACKAGE_PIN J17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[13] }]; #IO_L21N_T3_DQS_A18_15 Sch=fmc_la_n[13]
#set_property -dict { PACKAGE_PIN K17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[13] }]; #IO_L21P_T3_DQS_15 Sch=fmc_la_p[13]
#set_property -dict { PACKAGE_PIN H22   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[14] }]; #IO_L7N_T1_AD2N_15 Sch=fmc_la_n[14]
#set_property -dict { PACKAGE_PIN J22   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[14] }]; #IO_L7P_T1_AD2P_15 Sch=fmc_la_p[14]
#set_property -dict { PACKAGE_PIN K16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[15] }]; #IO_L23N_T3_FWE_B_15 Sch=fmc_la_n[15]
#set_property -dict { PACKAGE_PIN L16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[15] }]; #IO_L23P_T3_FOE_B_15 Sch=fmc_la_p[15]
#set_property -dict { PACKAGE_PIN G18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[16] }]; #IO_L4N_T0_15 Sch=fmc_la_n[16]
#set_property -dict { PACKAGE_PIN G17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[16] }]; #IO_L4P_T0_15 Sch=fmc_la_p[16]
#set_property -dict { PACKAGE_PIN B18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la17_cc_n }]; #IO_L11N_T1_SRCC_16 Sch=fmc_la17_cc_n
#set_property -dict { PACKAGE_PIN B17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la17_cc_p }]; #IO_L11P_T1_SRCC_16 Sch=fmc_la17_cc_p
#set_property -dict { PACKAGE_PIN C17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la18_cc_n }]; #IO_L12N_T1_MRCC_16 Sch=fmc_la18_cc_n
#set_property -dict { PACKAGE_PIN D17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la18_cc_p }]; #IO_L12P_T1_MRCC_16 Sch=fmc_la18_cc_p
#set_property -dict { PACKAGE_PIN A19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[19] }]; #IO_L17N_T2_16 Sch=fmc_la_n[19]
#set_property -dict { PACKAGE_PIN A18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[19] }]; #IO_L17P_T2_16 Sch=fmc_la_p[19]
#set_property -dict { PACKAGE_PIN F20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[20] }]; #IO_L18N_T2_16 Sch=fmc_la_n[20]
#set_property -dict { PACKAGE_PIN F19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[20] }]; #IO_L18P_T2_16 Sch=fmc_la_p[20]
#set_property -dict { PACKAGE_PIN D19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[21] }]; #IO_L14N_T2_SRCC_16 Sch=fmc_la_n[21]
#set_property -dict { PACKAGE_PIN E19   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[21] }]; #IO_L14P_T2_SRCC_16 Sch=fmc_la_p[21]
#set_property -dict { PACKAGE_PIN D21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[22] }]; #IO_L23N_T3_16 Sch=fmc_la_n[22]
#set_property -dict { PACKAGE_PIN E21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[22] }]; #IO_L23P_T3_16 Sch=fmc_la_p[22]
#set_property -dict { PACKAGE_PIN A21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[23] }]; #IO_L21N_T3_DQS_16 Sch=fmc_la_n[23]
#set_property -dict { PACKAGE_PIN B21   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[23] }]; #IO_L21P_T3_DQS_16 Sch=fmc_la_p[23]
#set_property -dict { PACKAGE_PIN B16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[24] }]; #IO_L7N_T1_16 Sch=fmc_la_n[24]
#set_property -dict { PACKAGE_PIN B15   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[24] }]; #IO_L7P_T1_16 Sch=fmc_la_p[24]
#set_property -dict { PACKAGE_PIN E17   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[25] }]; #IO_L2N_T0_16 Sch=fmc_la_n[25]
#set_property -dict { PACKAGE_PIN F16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[25] }]; #IO_L2P_T0_16 Sch=fmc_la_p[25]
#set_property -dict { PACKAGE_PIN E18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[26] }]; #IO_L15N_T2_DQS_16 Sch=fmc_la_n[26]
#set_property -dict { PACKAGE_PIN F18   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[26] }]; #IO_L15P_T2_DQS_16 Sch=fmc_la_p[26]
#set_property -dict { PACKAGE_PIN A20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[27] }]; #IO_L16N_T2_16 Sch=fmc_la_n[27]
#set_property -dict { PACKAGE_PIN B20   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[27] }]; #IO_L16P_T2_16 Sch=fmc_la_p[27]
#set_property -dict { PACKAGE_PIN B13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[28] }]; #IO_L8N_T1_16 Sch=fmc_la_n[28]
#set_property -dict { PACKAGE_PIN C13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[28] }]; #IO_L8P_T1_16 Sch=fmc_la_p[28]
#set_property -dict { PACKAGE_PIN C15   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[29] }]; #IO_L3N_T0_DQS_16 Sch=fmc_la_n[29]
#set_property -dict { PACKAGE_PIN C14   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[29] }]; #IO_L3P_T0_DQS_16 Sch=fmc_la_p[29]
#set_property -dict { PACKAGE_PIN A14   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[30] }]; #IO_L10N_T1_16 Sch=fmc_la_n[30]
#set_property -dict { PACKAGE_PIN A13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[30] }]; #IO_L10P_T1_16 Sch=fmc_la_p[30]
#set_property -dict { PACKAGE_PIN E14   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[31] }]; #IO_L4N_T0_16 Sch=fmc_la_n[31]
#set_property -dict { PACKAGE_PIN E13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[31] }]; #IO_L4P_T0_16 Sch=fmc_la_p[31]
#set_property -dict { PACKAGE_PIN A16   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[32] }]; #IO_L9N_T1_DQS_16 Sch=fmc_la_n[32]
#set_property -dict { PACKAGE_PIN A15   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[32] }]; #IO_L9P_T1_DQS_16 Sch=fmc_la_p[32]
#set_property -dict { PACKAGE_PIN F14   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_n[33] }]; #IO_L1N_T0_16 Sch=fmc_la_n[33]
#set_property -dict { PACKAGE_PIN F13   IOSTANDARD LVCMOS12 } [get_ports { fmc_la_p[33] }]; #IO_L1P_T0_16 Sch=fmc_la_p[33]
## }}}

set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 50 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
set_property BITSTREAM.CONFIG.CCLKPIN PULLNONE [current_design]
set_property CONFIG_MODE SPIx4 [current_design]
set_property CFGBVS VCCO [current_design]
set_property CONFIG_VOLTAGE 3.3 [current_design]

## Adding in any XDC_INSERT tags

## No XDC.INSERT tag in i2c
## From sysclk
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clksysclkctr/avgs*}]       -to [ get_cells -hier -filter {NAME =~*clksysclkctr/q_v*}]   8.0
## No XDC.INSERT tag in mem_flash_bkram
## No XDC.INSERT tag in zipscope
## From netbus
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_net/dbgtx_afifo/mem*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_net/dbgtx_afifo/GEN_REGISTERED_READ.o_rd_data*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_net/dbg_afifo/mem*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_net/dbg_afifo/GEN_REGISTERED_READ.o_rd_data*}] 8.0
## No XDC.INSERT tag in netdirs
## No XDC.INSERT tag in pwrcount
## No XDC.INSERT tag in alt
## No XDC.INSERT tag in rtccount
## No XDC.INSERT tag in buserr
## No XDC.INSERT tag in genclk
## No XDC.INSERT tag in spio
## No XDC.INSERT tag in wbu_arbiter
## No XDC.INSERT tag in zip_alt_uic
## No XDC.INSERT tag in zip_alt_mpc
## No XDC.INSERT tag in cfg
## No XDC.INSERT tag in KEYS
## No XDC.INSERT tag in RESET_ADDRESS
## No XDC.INSERT tag in iclock
## From net
create_clock -period 8.0 -name NETRX -waveform { 0.0 4.0 } -add [get_ports {i_net_rx_clk} ];

set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *afifo*/wgray_r*}] -to [ get_cells -hier -filter {NAME =~ *afifo*/wgray_cross*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *afifo*/rgray_r*}] -to [ get_cells -hier -filter {NAME =~ *afifo*/rgray_cross*}] 8.0

set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/o_net_reset*}]  -to [ get_cells -hier -filter {NAME =~*n_tx_reset*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_tx_reset*}]   -to [ get_cells -hier -filter {NAME =~*u_icmpstream/M_AXIN*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/*afifo*}]        -to [ get_cells -hier -filter {NAME =~*u_net/*afifo*/GEN_REGISTERED_READ.o_rd_data*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]    -to [ get_cells -hier -filter {NAME =~*net_core/preq_tx_reset*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/o_net_reset*}]  -to [ get_cells -hier -filter {NAME =~*net_core/q_tx_reset*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]    -to [ get_cells -hier -filter {NAME =~*u_net/u_icmpstream/M_AXIN_VALID*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]    -to [ get_cells -hier -filter {NAME =~*u_net/u_icmpstream/M_AXIN_DATA*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]    -to [ get_cells -hier -filter {NAME =~*u_net/u_icmpstream/M_AXIN_LAST*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/tfrtxspd/a_req*}]  -to [ get_cells -hier -filter {NAME =~*u_net/net_core/tfrtxspd/b_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/tfrtxspd/a_data*}] -to [ get_cells -hier -filter {NAME =~*u_net/net_core/tfrtxspd/o_b_data*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/hw_mac*}]       -to [ get_cells -hier -filter {NAME =~*txmaci/r_hw*}] 8.0

set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/tfrtxspd/b_last*}] -to [ get_cells -hier -filter {NAME =~ *tfrtxspd/a_pipe*}] 8.0



set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]       -to [ get_cells -hier -filter {NAME =~ *net_core/preq_rx_reset*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]       -to [ get_cells -hier -filter {NAME =~ *tfrrxspd/a_ack*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]       -to [ get_cells -hier -filter {NAME =~*tfrrxspd/a_pipe*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *sdrami/r_sys_reset*}]       -to [ get_cells -hier -filter {NAME =~ *tfrrxspd/a_req*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/o_net_reset_n*}]   -to [ get_cells -hier -filter {NAME =~ *n_rx_reset*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/o_net_reset_n*}]   -to [ get_cells -hier -filter {NAME =~ *q_rx_reset*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/tfrrxspd/b_last*}] -to [ get_cells -hier -filter {NAME =~ *tfrrxspd/a_pipe*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/my_ipaddr*}]       -to [ get_cells -hier -filter {NAME =~*o_no_match*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/my_ipaddr*}]       -to [ get_cells -hier -filter {NAME =~*o_match*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/my_ipaddr*}]       -to [ get_cells -hier -filter {NAME =~*rxipci/o_err*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/my_ipaddr*}]       -to [ get_cells -hier -filter {NAME =~*rxipci/o_err*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/hw_mac*}]          -to [ get_cells -hier -filter {NAME =~*arp/M_AXIN_DATA*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/hw_mac*}]          -to [ get_cells -hier -filter {NAME =~*rxmaci/r_hwmac*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/hw_mac*}]          -to [ get_cells -hier -filter {NAME =~*u_net/u_arp/M_AXIN_DATA*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/my_ipaddr*}]       -to [ get_cells -hier -filter {NAME =~*u_net/u_arp/M_AXIN_DATA*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~*u_net/net_core/tfr_rxipaddr/b_last*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~*u_net/net_core/tfr_rxipaddr/b_pipe*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~*u_net/net_core/tfr_rxipaddr/b_req*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~*u_net/arp_afifo/rgray_cross*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~*u_net/arp_afifo/wgray*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *tfr_rxipaddr/b_last*}]      -to [ get_cells -hier -filter {NAME =~*tfr_rxipaddr/a_pipe*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *tfr_rxipaddr/a_data*}]      -to [ get_cells -hier -filter {NAME =~*tfr_rxipaddr/o_b_data*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *tfr_rxipaddr/a_req*}]       -to [ get_cells -hier -filter {NAME =~*tfr_rxipaddr/o_b_data*}] 8.0
set_max_delay   -datapath_only -from [get_cells -hier -filter {NAME=~ *tfr_rxipaddr/a_req*}]       -to [ get_cells -hier -filter {NAME =~*tfr_rxipaddr/b_pipe*}] 8.0

set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/tfrrxspd/a_data*}] -to [ get_cells -hier -filter {NAME =~ *net_core/tfrrxspd/o_b_data*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~ *net_core/tfrrxspd/b_last*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~ *net_core/tfrrxspd/b_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_reset*}]      -to [ get_cells -hier -filter {NAME =~ *net_core/tfrrxspd/b_req*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_crcerr*}]     -to [ get_cells -hier -filter {NAME =~ *net_core/rx_crc_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/tfrrxspd/a*}]      -to [ get_cells -hier -filter {NAME =~ *net_core/tfrrxspd/b*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_miss*}]       -to [ get_cells -hier -filter {NAME =~ *net_core/rx_miss_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/tfr_*/a_data*}]       -to [ get_cells -hier -filter {NAME =~ *u_net/tfr*/o_b_data*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/tfr_*/a_req*}]       -to [ get_cells -hier -filter {NAME =~ *u_net/tfr*/b_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/tfr_*/b_last*}]       -to [ get_cells -hier -filter {NAME =~ *u_net/tfr*/a_pipe*}] 8.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *u_net/net_core/n_rx_err*}]       -to [ get_cells -hier -filter {NAME =~ *u_net/net_core/rx_err_pipe*}] 8.0
## No XDC.INSERT tag in zip_alt_uoc
## No XDC.INSERT tag in zip_alt_upc
## No XDC.INSERT tag in buildtime
## No XDC.INSERT tag in mdio
## No XDC.INSERT tag in REGDEFS
## No XDC.INSERT tag in zip_alt_mtc
## No XDC.INSERT tag in DEFAULT
## No XDC.INSERT tag in flash
## From genclkfb
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *thedesign/r_genclk_data*}]    -to [get_cells -hier -filter {NAME =~ *lowserdes*}] 10.0;

## No XDC.INSERT tag in zip_alt_utc
## From hdmi
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pix_reset_sys*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pix_reset_reg}] 5.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pix_reset_sys*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pix_reset_pipe*}] 5.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pix_reset_sys*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_framebuf/GEN_ASYNC_FIFO.r_pix_reset*}] 5.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_framebuf/GEN_ASYNC_FIFO.pxfifo/rgray*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_framebuf/GEN_ASYNC_FIFO.pxfifo/rgray_cross*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_framebuf/GEN_ASYNC_FIFO.pxfifo/wgray*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_framebuf/GEN_ASYNC_FIFO.pxfifo/wgray_cross*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_HDMIIN_TO_AXIVID.u_hdmi2vga/bitsync/*sync/pixloc/REQUIRE_QUALITY.o_val*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pre_wb_data*}] 10.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_HDMIIN_TO_AXIVID.u_hdmi2vga/bitsync/*sync/sync_valid*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pre_wb_data*}] 10.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_HDMIIN_TO_AXIVID.u_hdmi2vga/bitsync/all_locked*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/pre_wb_data*}] 10.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_new_frame/b_last*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_new_frame/a_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_new_frame/a_req*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_new_frame/b_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/b_last*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/a_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/a_req*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/b_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/a_data*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_px2sys/o_b_data*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/a_data*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/o_b_data*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/b_last*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/a_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/a_req*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_sys2px/b_pipe*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_mem2pix/cmap_reg*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/GEN_FRAMEBUF.u_mem2pix/cmap*reg*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~u_xpxclk/prepx/r_sel*}] -to [get_cells -hier -filter {NAME=~ u_xpxclk/prepx/u_bufg*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~thedesign/u_hdmi/u_pixclk_counter/avgs*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_pixclk_counter/q_v*}] 7.0
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~thedesign/u_hdmi/u_siclk_counter/avgs*}] -to [get_cells -hier -filter {NAME=~ thedesign/u_hdmi/u_siclk_counter/q_v*}] 7.0
## No XDC.INSERT tag in SIM
## No XDC.INSERT tag in uart
## No XDC.INSERT tag in altpic
## No XDC.INSERT tag in version
## From nettxctr
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clknettxctrctr/avgs*}]     -to [get_cells -hier -filter {NAME=~*clknettxctrctr/q_*}]        8
## From netclockctr
set_max_delay -datapath_only -from [get_cells -hier -filter {NAME=~ *clknetclockctrctr/avgs*}]     -to [get_cells -hier -filter {NAME=~*clknetclockctrctr/q_*}]        8
## No XDC.INSERT tag in XDC
## No XDC.INSERT tag in zip
## No XDC.INSERT tag in wbwide
## No XDC.INSERT tag in wb32
## From sdio
set_property -dict { PULLTYPE PULLUP } [get_ports io_sd_cmd]
## No XDC.INSERT tag in gpio
## No XDC.INSERT tag in edid
## No XDC.INSERT tag in flashcfg
## No XDC.INSERT tag in mem_bkram_only
## No XDC.INSERT tag in rtcdate
## No XDC.INSERT tag in wbu
## No XDC.INSERT tag in TMA
## No XDC.INSERT tag in bkram
## No XDC.INSERT tag in crossflash
## No XDC.INSERT tag in sdram
## No XDC.INSERT tag in syspic
## From masterclk
set_false_path -from [get_cells -hier -filter {NAME=~ pll_reset*}] -to [get_cells -hier -filter {NAME=~ net*/reset_pipe*}]
set_false_path -from [get_cells -hier -filter {NAME=~ pll_reset*}] -to [get_cells -hier -filter {NAME=~ net*/sync_reset*}]
## No XDC.INSERT tag in zip_alt_mic
## No XDC.INSERT tag in edidslv
## No XDC.INSERT tag in zip_alt_moc
## No XDC.INSERT tag in vadj33
## No XDC.INSERT tag in zip_tmb
## No XDC.INSERT tag in crossbus
## No XDC.INSERT tag in zip_tmc
## No XDC.INSERT tag in REGISTER
## No XDC.INSERT tag in zip_dmac
## No XDC.INSERT tag in rtc
## No XDC.INSERT tag in zip_jiffies
