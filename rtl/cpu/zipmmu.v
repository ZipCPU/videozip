////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	zipmmu.v
//
// Project:	Zip CPU backend for the GNU Compiler Collection
//
// Purpose:	To provide a "bump-in-the-line" wishbone memory management
//		unit, that is configured from one wishbone bus and modifies a
//	separate wishbone bus.  Both busses will not be active at the same time.
//
//	The idea is that the CPU can use one portion of its peripheral
//	system memory space to configure the MMU, and another portion of its
//	memory space to access the MMU.  Even more, configuring the MMU is to
//	be done when the CPU is in supervisor mode.  This means that all
//	high-memory, system-peripheral accesses will be enabled *only* when
//	the CPU is in supervisor mode.
//
//	There is a very specific reason for this design choice: by designing
//	the MMU in this fashion, the MMU may then be inluded (or not) at the
//	discretion of the individual assembling the ZipSystem (or equivalent)
//	module.
//
// Design Goals:
//
//	Since we're trying to design this for disadvantaged, limited CPUs,
//	we should be able to offer such CPUs only as much MMU as they want.
//	Therefore, it should be possible to scale the MMU up and/or down in
//	LUT space.
//
// Memory space:
//	1. On access via the memory bus, the MMU should provide for a speed
//		going through it such that any access is delayed by only one
//		clock cycle.  Further, multiple accesses to the same page
//		should not take any longer than the one cycle delay.  Accesses
//		to other pages should take a minimum number of clocks.
//		Accesses from one page to the next, such as from one page to
//		the next subsequent one, should cost no delays.
//
//	2. One independent control word to set the current context
//
//	  - When context = 0, virtual page = physical page, page table is an
//		unused pass through.
//	  - When context != 0, MMU translation is active anytime the GIE is
//		set.  Pages must match context, as well as virtual address.
//
//	  - Contains 4 RdOnly bits indicating the log address size for the
//		machine, offset by 17.  Thus, the build will have an address
//		bus of width (lgpage+17), or a memory space of (2^(lgpage+17)).
//		Under this formula, the number of valid address bits can range
//		from 17 to 32.
//	  -  Contains 4 RdOnly bits indicating log_2 TLB table size.
//	  	Size is given by (2^(lgsize)).  I'm considering sizes of 6,7&8
//	  -  Contains 4 RdOnly bits indicating the log page size, offset by
//		eight.  Page sizes are therefore given by (2^(lgpage+8)), and
//		the smallest page size is 256 words.
//	  - Contains 4 RdOnly bits indicating the log context size, offset by 1.
//		The number of bits in the context word therefore run from 1 to
//		(lgcontext+1)-1, supporting between (2^1)-1=3 and
//		(2^16)-1 = 65535 contexts.  (The zero context is not being
//		counted here, as it is special.)
//
//	+------+------+------+------+--------------------+
//	|      |      |      |      |                    |
//	|  4b  |  4b  |  4b  |  4b  |       16-bit       |
//	| LGADR| LGTBL|LGPGSZ|LGCTXT|    Context word    |
//	|      |      |      |      |                    |
//	+------+------+------+------+--------------------+
//
//	Supervisor *cannot* have page table entries, since there are no
//	interrupts (page faults) allowed in supervisor context.
//
//	To be valid,
//	  Context Size (1..16), NFlags (    4) < Page Size (8-23 bits)
//	  Page size (8-23 bits)                > NFlags bits (4)
//
//	Small page sizes, then, mean fewer contexts are possible
//
//	3. One status word, which contains the address that failed and some
//		flags:
//
//	Top Virtual address bits indicate which page ... caused  a problem.
//		These will be the top N bits of the word, where N is the size
//		of the virtual address bits.  (Bits are cleared upon any write.)
//
//	Flags: (Up to 12 bits, all zeros means no fault.  Bits are cleared upon
//		write)
//		- 4: Multiple page table matches
//		- 2: Attempt to write a read-only page
//		- 1: Page not found
//
//	3. Two words per active page table entry, accessed through two bus
//		addresses.  This word contains:
//
//	  16-bits	Page context
//	  20-bits	Virtual address
//	  20-bits	Physical address
//				A physical address of all ones means that the
//				page does not exist, and any attempt to access
//				the virtual address associated with this page
//				should fault.
//
//	Flags:
//	   1-bit	Read-only / ~written (user set/read/written)
//				If set, this page will cause a fault on any
//				attempt to write this memory.
//	   1-bit	This page may be executed
//	   1-bit	Cacheable
//				This is not a hardware page, but a memory page.
//				Therefore, the values within this page may be
//				cached.
//	   1-bit	Accessed
//				This an be used to implement a least-recently
//				used measure.  The hardware will set this value
//				when the page is accessed.  The user can also
//				set or clear this at will.
//
//		(Loaded flag	Not necessary, just map the physical page to 0)
//
//	We could equivalently do a 16-bit V&P addresses, for a 28-bit total
//	address space, if we didn't want to support the entire 32-bit space.
//
//
//	4. Can read/write this word in two parts:
//
//		(20-bit Virtual )(8-bits lower context)(4-bit flags), and
//		(20-bit Physical)(8-bits upper context)(4-bit flags)
//
//		Actual bit lengths will vary as the MMU configuration changes,
//		however the flags will always be the low order four bits,
//		and the virtual/physical address flags will always consume
//		32 bits minus the page table size.  The context bits will
//		always be split into upper and lower context bits.  If there
//		are more context bits than can fit in the space, then the
//		upper bits of the context field will be filled with zeros.
//
//		On any write, the context bits will be set from the context
//		bits in the control register.
//
//	+----+----+-----+----+----+----+----+--+--+--+--+
//	|                         | Lower 8b| R| E| C| A|
//	|  20-bit Virtual page ID | Context | O| X| C| C|
//	|(top 20 bits of the addr)|   ID    | n| E| H| C|
//	|                         |         | W| F| E| S|
//	+----+----+-----+----+----+----+----+--+--+--+--+
//
//	+----+----+-----+----+----+----+----+--+--+--+--+
//	|                         | Upper 8b| R| A| C| T|
//	|  20-bit Physical pg ID  | Context | O| C| C| H|
//	|(top 20 bits of the      |   ID    | n| C| H| S|
//	|    physical address)    |         | W| S| E| P|
//	+----+----+-----+----+----+----+----+--+--+--+--+
//
//	5. PF Cache--handles words in both physical and virtual
//	- On any pf-read, the MMU returns the current pagetable/TBL mapping
//		This consists of [Context,Va,Pa].
//	- The PF cache stores this with the address tag.  (If the PF is reading,
//		the VP should match, only the physical page ID needs to be
//		sored ...)
//	- At the end of any cache line read, the page table/TBL mapping address
//		will have long been available, the "Valid" bit will be turned
//		on and associated with the physical mapping.
//	- On any data-write (pf doesn't write), MMU sends [Context,Va,Pa]
//		TLB mapping to the pf-cache.
//	- If the write matches any physical PF-cache addresses (???), the
//		pfcache declares that address line invalid, and just plain
//		clears the valid bit for that page.
//
//	Since the cache lines sizes are smaller than the page table sizes,
//	failure to match the address means ... what?
//
//
//	6. Normal operation and timing:
//	  - One clock lost if still on the same page as last time, or in the
//		supervisor (physical pages only) context ...
//	  - Two clocks (1-more delay) if opening a new page.
//		(1-clock to look up the entry--comparing against all entries,
//		1-clock to read it, next clock the access goes forward.)
//	  - No more than two stalls for any access, pipelineable.  Thus, once
//		you've stalled by both clocks, you'll not stall again during
//		any pipeline operation.
//
//
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2016-2018, Gisselquist Technology, LLC
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
`default_nettype	none
//
`define	ROFLAG	3	// Read-only flag
`define	EXEFLG	2	// No-execute flag (invalid for I-cache)
`define	CHFLAG	1	// Cachable flag
`define	AXFLAG	0	// Accessed flag
//
module zipmmu(i_clk, i_reset, i_wbs_cyc_stb, i_wbs_we, i_wbs_addr,
				i_wbs_data, o_wbs_ack, o_wbs_stall, o_wbs_data,
		i_wbm_cyc, i_wbm_stb, i_wbm_we, i_wbm_exe,
			i_wbm_addr, i_wbm_data, i_wbm_sel, i_gie,
		o_cyc, o_stb, o_we, o_addr, o_data, o_sel,
			i_stall, i_ack, i_err, i_data,
			o_rtn_stall, o_rtn_ack, o_rtn_err,
				o_rtn_miss, o_rtn_data,
		pf_return_stb, pf_return_we,
				pf_return_p, pf_return_v,
				pf_return_cachable);
	parameter	// The size of the address bus.  Actual addressable
			// size will likely be 2^(ADDRESS_WIDTH+2) octets
			ADDRESS_WIDTH=28,
			// Number of page table entries
			LGTBL=4'h6,
			// The requested log page size in 8-bit bytes
			PLGPGSZB=20,
			// Number of bits describing context
			PLGCTXT=16;
	parameter [0:0] OPT_DELAY_RETURN = 1'b0;
	localparam	// And for our derived parameters (don't set these ...)
			// Width of the data bus is 32-bits.  This may be hard
			// to change.
			DW = 32,
			// AW is just shorthand for the name ADDRESS_WIDTH
			AW = ADDRESS_WIDTH,
			// Page sizes must allow for a minimum of one context
			// bit per page, plus four flag bits, hence the minimum
			// number of bits for an address within a page is 5
			LGPGSZB=(PLGPGSZB < 5)? 5:PLGPGSZB,	// in bytes
			LGPGSZW=LGPGSZB-2,			// in words
			// The context value for a given page can be split
			// across both virtual and physical words.  It cannot
			// have so many bits to it that it takes more bits
			// then are available.
			LGCTXT=((2*LGPGSZB-4)>PLGCTXT)?
				PLGCTXT:(2*LGPGSZB-4),
			// LGLCTX is the number of context bits in the low word
			LGLCTX=(LGCTXT > (LGPGSZB-4))?(LGPGSZB-4):LGCTXT,
			// LGHCTX is the number of context bits in the high word
			LGHCTX= (LGCTXT-LGLCTX>0)?(LGCTXT-LGLCTX):0,
			VAW=(DW-LGPGSZB), //  Virtual address width, in bytes
			PAW=(AW-LGPGSZW), // Physical address width, in words
			TBL_BITS = LGTBL,	// Bits necessary to addr tbl
			TBL_SIZE=(1<<TBL_BITS);// Number of table entries
	input	wire		i_clk, i_reset;
	//
	input	wire		i_wbs_cyc_stb;
	input	wire		i_wbs_we;
	input	wire	[(LGTBL+1):0]	i_wbs_addr;
	input	wire	[(DW-1):0]	i_wbs_data;
	output	reg			o_wbs_ack;
	output	wire			o_wbs_stall;
	output	reg	[(DW-1):0]	o_wbs_data;
	//
	input	wire		i_wbm_cyc, i_wbm_stb;
	//
	input	wire			i_wbm_we, i_wbm_exe;
	input	wire [(DW-2-1):0]	i_wbm_addr;
	input	wire [(DW-1):0]		i_wbm_data;
	input	wire [(DW/8-1):0]	i_wbm_sel;
	input	wire			i_gie;
	//
	// Here's where we drive the slave side of the bus
	output	reg			o_cyc;
	output	wire			o_stb, o_we;
	output	reg	[(AW-1):0]	o_addr;
	output	reg	[(DW-1):0]	o_data;
	output	reg	[(DW/8-1):0]	o_sel;
	// and get our return information from driving the slave ...
	input	wire			i_stall, i_ack, i_err;
	input	wire	[(DW-1):0]	i_data;
	//
	// Here's where we return information on either our slave/control bus
	// or the memory bus we are controlled from.  Note that we share these
	// wires ...
	output	wire		o_rtn_stall;
	output	wire		o_rtn_ack;
	output	wire		o_rtn_err, o_rtn_miss;
	output	wire [(DW-1):0]	o_rtn_data;
	// Finally, to allow the prefetch to snoop on the MMU conversion ...
	output	wire			pf_return_stb, // snoop data is valid
					pf_return_we; // snoop data is chnging
	output	wire	[(PAW-1):0]	pf_return_p;
	output	wire	[(VAW-1):0]	pf_return_v;
	output	wire			pf_return_cachable;
	//
	//

//
//
//
	reg	[3:1]			tlb_flags	[0:(TBL_SIZE-1)];
	reg	[(LGCTXT-1):0]		tlb_cdata	[0:(TBL_SIZE-1)];
	reg	[(VAW-1):0]		tlb_vdata	[0:(TBL_SIZE-1)];
	reg	[(PAW-1):0]		tlb_pdata	[0:(TBL_SIZE-1)];
	reg	[(TBL_SIZE-1):0]	tlb_valid, tlb_accessed;

	wire	adr_control, adr_vtable, adr_ptable;
	wire	wr_control, wr_vtable, wr_ptable;
	wire	[(LGTBL-1):0]	wr_tlb_addr;
	assign	wr_tlb_addr= i_wbs_addr[(LGTBL):1]; // Leave bottom for V/P
	assign	adr_control= (i_wbs_cyc_stb)&&(~i_wbs_addr[(LGTBL+1)])&&(~i_wbs_addr[0]);
	assign	adr_vtable = (i_wbs_cyc_stb)&&( i_wbs_addr[(LGTBL+1)])&&(~i_wbs_addr[0]);
	assign	adr_ptable = (i_wbs_cyc_stb)&&( i_wbs_addr[(LGTBL+1)])&&( i_wbs_addr[0]);
	assign	wr_control = (adr_control)&&(i_wbs_we);
	assign	wr_vtable  = (adr_vtable )&&(i_wbs_we);
	assign	wr_ptable  = (adr_ptable )&&(i_wbs_we);

	reg			z_context;
	wire			kernel_context;
	reg	[(LGCTXT-1):0]	r_context_word;
	//
	wire	[31:0]		w_control_data,w_vtable_reg,w_ptable_reg;
	reg	[31:0]	status_word;
	//
	//
	reg			r_pending, r_we, r_exe, r_valid,
				last_page_valid, last_ro, last_exe;
	reg	[(DW-3):0]	r_addr;
	reg	[(DW-1):0]	r_data;
	wire	[(VAW-1):0]	vpage;
	wire	[AW-LGPGSZW-1:0]	ppage;
	reg	[(DW/8-1):0]	r_sel;
	reg	[(PAW-1):0]	last_ppage;
	reg	[(VAW-1):0]	last_vpage;
	//
	wire	[(TBL_SIZE-1):0]	r_tlb_match;
	reg	[(LGTBL-1):0]		s_tlb_addr, last_tlb;
	reg				s_tlb_miss, s_tlb_hit, s_pending;
	//
	wire	ro_flag, exe_flag, simple_miss, ro_miss, exe_miss, table_err, cachable;
	reg	pf_stb, pf_cachable;
	reg	miss_pending;
	//
	reg	rtn_err;


	wire	this_page_valid, pending_page_valid;
	assign	this_page_valid = ((last_page_valid)
				&&(i_wbm_addr[(DW-3):(DW-2-VAW)]==last_vpage)
				&&((!last_ro)||(!i_wbm_we))
				&&((!last_exe)||(!i_wbm_exe)));
	assign	pending_page_valid = ((s_pending)&&(s_tlb_hit)
				&&((!r_we)||(!ro_flag))
				&&((!r_exe)||(exe_flag)));

	//////////////////////////////////////////
	//
	//
	// Step one -- handle the control bus--i_wbs_cyc_stb
	//
	//
	//////////////////////////////////////////
	always @(posedge i_clk)
	begin
		// Write to the Translation lookaside buffer
		if (wr_vtable)
			tlb_vdata[wr_tlb_addr]<=i_wbs_data[(DW-1):LGPGSZB];
		if (wr_ptable)
			tlb_pdata[wr_tlb_addr]<=i_wbs_data[(AW+1):LGPGSZB];
		// Set the context register for the page
		if (wr_vtable)
			tlb_flags[wr_tlb_addr] <= i_wbs_data[3:1];
		if (wr_vtable)
			tlb_cdata[wr_tlb_addr][(LGLCTX-1):0]
				<= i_wbs_data[(LGLCTX+4-1):4];
	end

	initial	tlb_accessed = 0;
	always @(posedge i_clk)
	if (i_reset)
		tlb_accessed <= 0;
	else begin
		if (wr_vtable)
			tlb_accessed[wr_tlb_addr] <= 1'b0;
		// Otherwise, keep track of the accessed bit if we
		// ever access this page
		else if ((!kernel_context)&&(pending_page_valid))
			tlb_accessed[s_tlb_addr] <= 1'b1;
		else if ((!kernel_context)&&(this_page_valid))
			tlb_accessed[last_tlb] <= 1'b1;
	end

	generate if (LGHCTX > 0)
	begin : HCTX
		always @(posedge i_clk)
		if (wr_ptable)
			tlb_cdata[wr_tlb_addr][(LGCTXT-1):LGLCTX]
				<= i_wbs_data[(LGHCTX+4-1):4];
	end endgenerate

	// Writing to the control word
	initial z_context = 1'b1;
	initial r_context_word = 0;
	always @(posedge i_clk)
	if (wr_control)
		begin
		r_context_word <= i_wbs_data[(LGCTXT-1):0];
		z_context      <= (i_wbs_data[(LGCTXT-1):0] == {(LGCTXT){1'b0}});
		end
	assign	kernel_context = (z_context)||(!i_gie);
	// Status words cannot be written to

	always @(posedge i_clk)
	if (i_reset)
		tlb_valid <= 0;
	else if (wr_ptable)
		tlb_valid[wr_tlb_addr]<=1'b1; //(i_wbs_data[(AW+1):LGPGSZB]!=0);

	/* v*rilator lint_off WIDTH */
	assign	w_control_data[31:28] = AW[3:0]-4'd1;
	assign	w_control_data[27:24] = LGTBL[3:0];
	assign	w_control_data[23:20] = LGPGSZB[3:0]-4'd10;
	assign	w_control_data[19:16] = LGCTXT[3:0]-1'b1;
	/* v*rilator lint_on WIDTH */
	assign	w_control_data[15: 0] = {{(16-LGCTXT){1'b0}}, r_context_word};
	//
	assign	w_vtable_reg[(DW-1):LGPGSZB] = tlb_vdata[wr_tlb_addr];
	assign	w_vtable_reg[(LGLCTX+4-1):4] = { tlb_cdata[wr_tlb_addr][(LGLCTX-1):0] };
	assign	w_vtable_reg[ 3:0]  = { tlb_flags[wr_tlb_addr], tlb_accessed[wr_tlb_addr] };
	//
	assign	w_ptable_reg[(DW-1):LGPGSZB] = { {(DW-PAW-LGPGSZB){1'b0}},
					tlb_pdata[wr_tlb_addr] };
	assign	w_ptable_reg[ 3:0]  = 4'h0;
	//
	generate
		if (4+LGHCTX-1>4)
			assign	w_ptable_reg[(4+LGHCTX-1):4] =  {
				tlb_cdata[wr_tlb_addr][(LGCTXT-1):LGLCTX] };
		if (LGPGSZB > LGLCTX+4)
			assign	w_vtable_reg[(LGPGSZB-1):(LGLCTX+4)] = 0;
		if (LGPGSZB > LGHCTX+4)
			assign	w_ptable_reg[(LGPGSZB-1):(LGHCTX+4)] = 0;
	endgenerate

	//
	// Now, reading from the bus
	/*
	wire	[(LGCTXT-1):0]	w_ctable_reg;
	assign	w_ctable_reg = tlb_cdata[wr_tlb_addr];
	reg			setup_this_page_flag;
	reg	[(LGCTXT-1):0]	setup_page;
	initial	setup_this_page_flag = 1'b0;
	always @(posedge i_clk)
		setup_page <= w_ctable_reg;
	always @(posedge i_clk)
		setup_this_page_flag <= (!i_reset)&&(i_wbs_cyc_stb)&&(i_wbs_addr[LGTBL+1]);
	*/



	//////////////////////////////////////////
	//
	//
	// Step two -- handle the page lookup on the master bus
	//
	//
	//////////////////////////////////////////

	//
	//
	// First clock, and the r_ register, copies the bus data from the bus.
	// While this increases the bus latency, it also gives us a moment to
	// work.
	//
	//
	wire	[(VAW-1):0]	r_vpage;
	wire	[(PAW-1):0]	r_ppage;
	assign	r_vpage = (r_addr[(DW-3):(DW-2-VAW)]);
	assign	r_ppage = (o_addr[(AW-1):LGPGSZW]);

	initial	s_pending = 1'b0;
	initial	r_pending = 1'b0;
	initial	r_valid   = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		r_pending <= 1'b0;
		r_valid   <= 1'b0;
		o_addr    <= 0;
		r_we      <= 0;
		r_exe     <= 0;
		r_addr    <= 0;
		r_data    <= 0;
		r_sel     <= 0;
		//
		s_pending <= 1'b0;
	end else
	begin
		if (!o_rtn_stall)
		begin
			r_pending <= (i_wbm_stb)&&(!kernel_context)
						&&(!this_page_valid);
			r_we      <= i_wbm_we;
			r_exe     <= i_wbm_exe;
			o_addr    <= { { (kernel_context)?
				i_wbm_addr[(AW-1):LGPGSZW] : last_ppage },
				i_wbm_addr[(LGPGSZW-1):0] };
			r_addr    <= i_wbm_addr;
			r_data    <= i_wbm_data;
			r_sel     <= i_wbm_sel;
			r_valid   <= (i_wbm_stb)&&((kernel_context)||(this_page_valid));
			s_pending <= 1'b0;
		end else if (!r_valid) begin
			r_valid <= (pending_page_valid);
			o_addr <= { ppage , r_addr[(LGPGSZW-1):0] };
			r_pending<= (r_pending)&&(!pending_page_valid);
			s_pending <=(r_pending)&&(!pending_page_valid);
		end else begin
			r_pending <= 1'b0;
			s_pending <= 1'b0;
		end

		if ((!i_wbm_cyc)||(o_rtn_err)||((o_cyc)&&(i_err)))
		begin
			s_pending <= 1'b0;
			r_pending <= 1'b0;
			r_valid   <= 1'b0;
		end
	end
	// Second clock: know which buffer entry this belong in.
	// If we don't already know, then the pipeline must be stalled for a
	// while ...
	genvar k, s;
	generate
	for(k=0; k<TBL_SIZE; k = k + 1)
		assign r_tlb_match[k] =
			// The page  must be valid
			(tlb_valid[k])
			// Virtual address must match
			&&(tlb_vdata[k] == r_vpage)
			// Context must match as well
			&&(tlb_cdata[k][LGCTXT-1:1] == r_context_word[LGCTXT-1:1])
			&&((!tlb_cdata[k][0])||(r_context_word[0]));
	endgenerate

	initial	s_tlb_miss = 1'b0;
	initial	s_tlb_hit  = 1'b0;
	generate
		integer i;
	always @(posedge i_clk)
	begin // valid when s_ becomes valid
		s_tlb_addr <= {(LGTBL){1'b0}};
		for(i=0; i<TBL_SIZE; i=i+1)
			if (r_tlb_match[i])
				s_tlb_addr <= i[(LGTBL-1):0];
		s_tlb_miss <= (r_pending)&&(r_tlb_match == 0);
		s_tlb_hit <= 1'b0;
		for(i=0; i<TBL_SIZE; i=i+1)
			if (r_tlb_match == (1<<i))
				s_tlb_hit <= (r_pending)&&(!r_valid)&&(i_wbm_cyc);
	end endgenerate

	// Third clock: Read from the address the virtual table offset,
	// whether read-only, etc.
	assign	ro_flag     = tlb_flags[s_tlb_addr][`ROFLAG];
	assign	exe_flag    = tlb_flags[s_tlb_addr][`EXEFLG];
	assign	simple_miss = (s_pending)&&(s_tlb_miss);
	assign	ro_miss     = (s_pending)&&(s_tlb_hit)&&(r_we)&&(ro_flag);
	assign	exe_miss    = (s_pending)&&(s_tlb_hit)&&(r_exe)&&(!exe_flag);
	assign	table_err   = (s_pending)&&(!s_tlb_miss)&&(!s_tlb_hit);
	assign	vpage       = tlb_vdata[s_tlb_addr];
	assign	ppage	    = tlb_pdata[s_tlb_addr];
	assign	cachable    = tlb_flags[s_tlb_addr][`CHFLAG];

	initial	pf_cachable = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		pf_cachable <= 1'b0;
	else
		pf_cachable <= cachable;

	initial	pf_stb = 1'b0;
	initial	last_ppage = 0;
	initial	last_vpage = 0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		pf_stb <= 1'b0;
		last_ppage <= 0;
		last_vpage <= 0;
		last_tlb   <= 0;
	end else if ((!kernel_context)&&(r_pending)&&(!last_page_valid))
	begin
		last_tlb   <= s_tlb_addr;
		last_ppage <= ppage;
		last_vpage <= vpage;
		last_exe   <= exe_flag;
		last_ro    <= ro_flag;
		pf_stb <= 1'b1;
	end else
		pf_stb <= 1'b0;

	initial	status_word = 0;
	always @(posedge i_clk)
	if (i_reset)
		status_word <= 0;
	else if (wr_control)
		status_word <= 0;
	else if ((table_err)||(ro_miss)||(simple_miss)||(exe_miss))
		status_word <= { r_vpage,
				{(LGPGSZB-4){1'b0}},
				(table_err), (exe_miss),
				(ro_miss), (simple_miss) };

	initial	last_page_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_page_valid <= 1'b0;
	else if ((i_wbs_cyc_stb)&&(i_wbs_we))
		last_page_valid <= 1'b0;
	else if (!kernel_context)
	begin
		if (!o_rtn_stall)
			// A new bus request
			last_page_valid <= (last_page_valid)
				&&(i_wbm_addr[(DW-3):(DW-2-VAW)] == last_vpage);
		else if ((r_pending)&&(!last_page_valid))
			last_page_valid <= (s_pending)&&(s_tlb_hit);
	end

	parameter	LGFIFO = 6;
	reg	[LGFIFO-1:0]	bus_outstanding;
	initial	bus_outstanding = 0;
	always @(posedge i_clk)
	if (i_reset)
		bus_outstanding <= 0;
	else if (!o_cyc)
		bus_outstanding <= 0;
	else case({ (o_stb)&&(!i_stall), (i_ack)||(i_err) } )
	2'b01: bus_outstanding <= bus_outstanding - 1'b1;
	2'b10: bus_outstanding <= bus_outstanding + 1'b1;
	default: begin end
	endcase

	reg	bus_pending;
	initial	bus_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
		bus_pending <= 0;
	else if (!o_cyc)
		bus_pending <= 1'b0;
	else case({ (o_stb)&&(!i_stall), ((i_ack)||(i_err)) })
	2'b01: bus_pending <= (bus_outstanding > 1);
	2'b10: bus_pending <= 1'b1;
	default: begin end
	endcase

	initial	rtn_err = 1'b0;
	initial	o_cyc   = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
	begin
		o_cyc <= 1'b0;
		rtn_err   <= 1'b0;
	end else begin
		o_cyc <=  (i_wbm_cyc)&&(!o_rtn_err)&&((!i_err)||(!o_cyc)); /// &&((o_cyc)||(r_valid));

		rtn_err  <= (i_wbm_cyc)&&(i_err)&&(o_cyc);
	end

	generate if (OPT_DELAY_RETURN)
	begin
		reg		r_rtn_ack;
		reg	[31:0]	r_rtn_data;

		initial	r_rtn_data = 0;
		initial	r_rtn_ack  = 0;
		always @(posedge i_clk)
		if (i_reset)
		begin
			r_rtn_ack  <= 0;
			r_rtn_data <= 0;
		end else begin
			r_rtn_ack  <= (i_wbm_cyc)&&(i_ack)&&(o_cyc);
			r_rtn_data <= i_data;
		end

		assign	o_rtn_ack  = r_rtn_ack;
		assign	o_rtn_data = r_rtn_data;
	end else begin

		assign	o_rtn_ack  = (i_ack)&&(o_cyc);
		assign	o_rtn_data = i_data;
	end endgenerate

	assign	o_stb = (r_valid);
	assign	o_we  =  (r_we);
	assign	o_rtn_stall = (i_wbm_cyc)&&(
			(o_rtn_err)
			||((r_pending)&&(!r_valid))
			||((o_stb)&&(i_stall))
			||(miss_pending));

	initial	miss_pending = 0;
	always @(posedge i_clk)
	if (i_reset)
		miss_pending <= 0;
	else if (!i_wbm_cyc)
		miss_pending <= 0;
	else
		miss_pending <= (i_wbm_cyc)&&(
				(simple_miss)||(ro_miss)||(exe_miss)
				||((s_pending)&&(!s_tlb_miss)&&(!s_tlb_hit)));

	assign	o_rtn_miss  = (miss_pending)&&(!bus_pending);
	assign	o_rtn_err   = (rtn_err);

	assign	o_sel  = r_sel;
	assign	o_data = r_data;

	//
	assign	o_wbs_stall = 1'b0;
	initial	o_wbs_ack = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_wbs_ack <= 1'b0;
	else
		o_wbs_ack <= (i_wbs_cyc_stb);
	always @(posedge i_clk)
	if (i_reset)
		o_wbs_data <= 0;
	else case({i_wbs_addr[LGTBL+1],i_wbs_addr[0]})
	2'b00: o_wbs_data <= w_control_data;
	2'b01: o_wbs_data <= status_word;
	2'b10: o_wbs_data <= w_vtable_reg;
	2'b11: o_wbs_data <= w_ptable_reg;
	endcase

	//
	// Bus snooping returns ...
	//
	assign	pf_return_stb = pf_stb;
	assign	pf_return_we = r_we;
	assign	pf_return_p  = last_ppage;
	assign	pf_return_v  = last_vpage;
	assign	pf_return_cachable = pf_cachable;

	// Also requires being told when/if the page changed
	// So, on a page change,
	// pf_return_we = 1
	// pf_stb = 1
	// and pf_return_p has the physical address

	// Make verilator happy
	// verilator lint_off UNUSED
	wire [(PAW-1):0]	unused;
	assign	unused = r_ppage;
	generate if (4+LGCTXT < LGPGSZB)
	begin
		wire	unused_data;
		assign	unused_data = i_wbs_data[LGPGSZB-1:4+LGCTXT];
	end endgenerate
	// verilator lint_on  UNUSED

endmodule
