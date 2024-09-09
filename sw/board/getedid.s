////////////////////////////////////////////////////////////////////////////////
//
// Filename:	getedid.s
// {{{
// Project:	VideoZip, a ZipCPU SoC supporting video functionality
//
// Purpose:	Describes an I2C CPU script for reading all I2C data from
//		(in this case) the EDID of the downstream monitor.
//
//	This file is designed to be processed via the i2casm compiler, as
//	in:
//
//	% i2casm -c getedid.i -o getedid.c
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
// }}}
// Copyright (C) 2024, Gisselquist Technology, LLC
// {{{
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of the GNU General Public License as published
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
// }}}
// License:	GPL, v3, as defined and found on www.gnu.org,
// {{{
//		http://www.gnu.org/licenses/gpl.html
//
////////////////////////////////////////////////////////////////////////////////
// }}}
get_edid_script:
	CHAN	0
	START
	SEND	0xa0|WR
	SEND	0x00	// Address 0
	START
	SEND	0xa0|RD
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXK
	RXLN
	STOP
	HALT
