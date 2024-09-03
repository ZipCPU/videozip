void	i2c_clear(I2CCPU * const c) {
	unsigned	counts;

	if (I2CC_MANUAL & c->ic_override) {
		// Clear any manual indication
		//	"Issue" HALT commands, 9 and 9
		c->ic_override = 0x099;
	}

	c->ic_control = I2CC_ABORT | I2CC_ERROR | I2CC_HALT;
	counts = 16*c->ic_clkcount;
	while(counts > 0 && 0 == (I2CC_STOPPED & c->ic_control))
		counts--;
	if (0 == (I2CC_STOPPED & c->ic_control)) {
		c->ic_control = I2CC_ABORT | I2CC_ERROR | I2CC_HALT | I2CC_HARDHALT;
	} counts = 4*c->ic_clkcount;
	while(counts > 0 && 0 == (I2CC_STOPPED & c->ic_control))
		counts--;
	
	// Set: CLK = ( SYSRATE / CKRATE / 4) - 1
	c->ic_clkcount = (100000000 / 3 / 100000)-1;
}

void	i2c_dump(I2CCPU * const c) {
	unsigned	ctrl, ovr, addr, clk;

	ctrl = c->ic_control;
	ovr  = c->ic_override;
	addr = c->ic_address;
	clk  = c->ic_clkcount;

	printf("I2C-DUMP @0x%08x:\n", (unsigned)c);
	printf("\tCTRL : 0x%08x\n", ctrl);
	if (ctrl & I2CC_WAITING) printf("\t\tWAITING\n");	// 0x0800000
	if (ctrl & I2CC_HALT) printf("\t\tHALTED\n");	// 0x0400000
	if (ctrl & I2CC_ABORT) printf("\t\tABORT\n");
	if (ctrl & I2CC_ERROR) printf("\t\tERROR\n");
	if (ctrl & I2CC_HARDHALT) printf("\t\tHARDHALT\n");
	if (ctrl & I2CC_SCL) printf("\t\tSCL\n");
	if (ctrl & I2CC_SDA) printf("\t\tSDA\n");
	if (ctrl & I2CC_STOPPED) printf("\t\tSTOPPED\n");
	if (ctrl & I2CC_FAULT) printf("\t\tFAULT!\n");
	if (ctrl & 0x100000) printf("\t\tERR\n");
	// HARD HALT
	if (ctrl & 0x040000) printf("\t\tVLD\n");
	if (ctrl & 0x020000) printf("\t\tHLF: %1x\n", (ctrl >> 28)&0x0f);
	if (ctrl & 0x010000) printf("\t\tIMM\n");
	if (ctrl & 0x008000) printf("\t\tSCL-OUT\n");
	if (ctrl & 0x004000) printf("\t\tSDA-OUT\n");
	if (ctrl & 0x002000) printf("\t\tSCL\n");
	if (ctrl & 0x001000) printf("\t\tSDA\n");
		printf("\t\tINSN: 0x%03x\n", ctrl & 0x0fff);
	// if (ctrl & I2CC_CLEAR) printf("\t\tSDA\n");
	printf("\tOVR  : 0x%08x\n", ovr);
	if (I2CC_MANUAL & ovr) printf("\t\tMANUAL\n");
	if (I2CC_MANSCL & ovr) printf("\t\tMAN SCL\n");
	if (I2CC_MANSDA & ovr) printf("\t\tMAN SDA\n");
	if (I2CC_TVALID & ovr) printf("\t\tTVALID\n");
	if (I2CC_TLAST  & ovr) printf("\t\tTLAST\n");
		printf("\t\tINSN : 0x%08x\n", ovr & 0x0ff);
	printf("\tADDR : 0x%08x\n", addr);
	printf("\tCLK  : 0x%08x\n", clk);
		printf("\t\tRATE : %f\n", 100000000.0 / (clk+1) / 3.0);
		// CKRATE = SYSRATE / (CLK+1) / 3.0
		// Set: CLK = ( SYSRATE / CKRATE / 3) - 1
}

/*
void	i2c_release(I2CCPU *c) {
	// c->ic_control
	//
	// IF !CLK && !DATA (but o_data)
	//	RAISE CLK
	// IF CLK && !DATA (but o_data)
	//	LOWER CLK
}
*/

