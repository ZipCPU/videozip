state <= startup
iop_state_select <= init_operation[14]
iop_res_set	<= init_operation[13]
iop_res_val	<= init_operation[12]
iop_vdd_set	<= init_operation[11]	0
iop_vdd_val	<= init_operation[10]	0
iop_vbat_set	<= init_operation[9]	0
iop_vbat_val	<= init_operation[8]	0
iop_data	<= init_operation[7:0]

1901	VDD = 0, DELAY 1 .. ?
51ae	res_val = 1, 
2101	SET RESET = 0, DELAY 1 ms
3101	SET_RESET = 1, DELAY 1 ms
518d	Set charge pump to 14
5114	(Charge pump parameter)
51d9	Set pre-charge period to F1
51f1	(Argument to last line)
1264	SET VBAT, DELAY 64 ms
5081	Set contrast control to 0x0f
500f	(Argument to contrast control)
50a0	Set Segment Re-map, column address 0 is mapped to SEG0 (RESET)
50c0	Set output scan direcction to NORMAL mode
50da	Set com pins h/w configuration, sequential COM pin, Disable COM lR remap
5000	( Set lower nibble of column start address to  0 )
50af	Display ON in normal mode

