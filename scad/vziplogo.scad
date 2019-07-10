vzlogow = 41;
vzlogol = 9;
vzlogob = 2;
vzlogoh = 5;
module	vziplogo() {
	linear_extrude(height=vzlogoh) {
		union() {
			// V
			polygon(points=[
				[0,0],
				[1,0],
				[10,9],
				[9,9],
				[1,1],
				[4,9],
				[3,9] ]);
			// I
			polygon(points=[
				[3,0],
				[4,0],
				[11,7],
				[10,7] ]);
			// The 'D'
			polygon(points=[
				[6,0],
				[7,0],
				[13,6],
				[15,6],
				[15,5],
				[12,2],
				[10,1],
				[ 9,1],
				[ 8,0],
				[10,0],
				[12,1],
				[16,5],
				[16,7],
				[13,7],
				[ 6,0] ]);
			// The E
			polygon(points=[
				[13,0],
				[18,0],
				[19,1],
				[15,1],
				[17,3],
				[20,3],
				[21,4],
				[18,4],
				[20,6],
				[24,6],
				[25,7],
				[20,7] ]);
			// The O
			polygon(points=[
				[22,0.9],
				[22,0],
				[25,0],
				[31,6],
				[31,7],
				[27,7],
				[22,2],
				[22,1.1],
				[27,6],
				[30,6],
				[25,1] ]);
		/*
			// The Z
			polygon(points=[
				[25,-2],
				[30,-2],
				[31,-1],
				[27,-1],
				[37,9],
				[27,9],
				[26,8],
				[35,8]]);
			// The i
			polygon(points=[
				[31,0],
				[32,0],
				[34,2],
				[33,2],
				[31,0]]);
			polygon(points=[
				[34,3],
				[35,3],
				[36,4],
				[35,4] ]);
			// The p
			polygon(points=[
				[32,-2],
				[33,-2],
				[37,2],
				[40,2],
				[39,1],
				[37,1],
				[36,0],
				[39,0],
				[41,2],
				[41,3],
				[37,3] ]);
		*/
		}
	}
}

// vziplogo();
// translate([0,-vzlogob,-vzlogoh]) color("red") cube([vzlogow, vzlogol+vzlogob, vzlogoh]);

