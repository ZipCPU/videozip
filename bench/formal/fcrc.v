module fcrc(i_clk, i_reset, i_v, i_d, o_v, o_d, o_err);
	input	wire		i_clk, i_reset;
	input	wire		i_v;
	input	wire	[7:0]	i_d;
	output	wire		o_v;
	output	wire	[7:0]	o_d;
	output	wire		o_err;

	wire		tx_v;
	wire	[7:0]	tx_d;
	addecrc tx(i_clk, i_reset, 1'b1, 1'b1, i_v, i_d, tx_v, tx_d);
	rxecrc  rx(i_clk, i_reset, 1'b1, 1'b1, tx_v, tx_d, o_v, o_d, o_err);

	always @(*)
		assert(!o_err);
endmodule
