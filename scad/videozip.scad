include <GT.scad>
include <zipcpu.scad>
include <vziplogo.scad>

module videozip() {
	// Top left is power, right side is the FMC connector
	dim = 134.5;
	height = 10;
	tol = 0.1;

	module cutout(x, y, w, h, v) {
		ex = 1.5;
		translate([x-ex/2,y-ex/2,-tol/2])
			cube([w+ex,h+ex,v+tol]);
	}

	module keepit(x, y, w, h, v) {
		ex = -1.5;
		translate([x-ex/2,y-ex/2,-tol/2])
			cube([w+ex,h+ex,v+tol]);
	}

	module	oledcutout() {
		h = height+0.1;
		lft = 51.05;
		rht = 82.80;
		bot = 25.5;
		top = 37.0;
		//
		lftx = lft-1.20*h;
		rhtx = rht+0.65*h;
		botx = bot-0.50*h;
		topx = top+1.80*h;

		// OLED
		cutout(51.05,25.5,31.75,11.5, h);
		// Build a ramp around the OLED
		/*
		polyhedron(
			points = [
				// Start with the base
				[ lft, bot, -0.05 ],	// Bottom left
				[ rht, bot, -0.05 ],	// Bottom right
				[ rht, top, -0.05 ],	// Top right
				[ lft, top, -0.05 ],	// Top left
				// Now the points on the top
				[ lftx, botx, h ],	// Bottom left
				[ rhtx, botx, h ],	// Bottom right
				[ rhtx, topx, h ],	// Top right
				[ lftx, topx, h ]	// Top left
				], faces = [
				[ 0, 1, 2, 3 ],
				[ 0, 1, 5, 4 ],
				[ 1, 2, 6, 5 ],
				[ 2, 3, 7, 6 ],
				[ 3, 0, 4, 7 ],
				[ 4, 5, 6, 7 ]
				// Now for the corners
				// [ 0,  8, 4, 12 ],
				// [ 1,  9, 5, 13 ],
				// [ 2, 10, 6, 14 ],
				// [ 3, 11, 7, 15 ]
				], convexity=3);
		*/
	}

	module layer(n) {
		base = (n==0) ? 0
			: (n == 1) ? 1.5
			: (n == 2) ? 2.4
			: (n == 3) ? 5.0
			: (n == 4) ? 5.95
			: (n == 5) ? 6.65
			: (n == 6) ? 7.0
			: (n == 7) ? 7.8
			: height;

		ztmp = (n==0) ? 1.5
			: (n==1) ? 2.4
			: (n==2) ? 5.0
			: (n==3) ? 5.95
			: (n==4) ? 6.65
			: (n==5) ? 7.0
			: (n==6) ? 7.8
			: height;

		zh = ztmp - base;
		above = height;

		// Heat sink
		cutout(78.35-21.5,78.6-23.05,21.5,23.05, above);

		// Switches
		cutout(85.9-61.7, 0, 61.7, 13.25, above);

		// LEDs
		cutout(26.40,16.75,1,3,above);
		cutout(34.40,16.75,1,3,above);
		cutout(42.40,16.75,1,3,above);
		cutout(50.40,16.75,1,3,above);
		cutout(58.40,16.75,1,3,above);
		cutout(66.40,16.75,1,3,above);
		cutout(74.40,16.75,1,3,above);
		cutout(82.40,16.75,1,3,above);

		
		//translate([85.9-61.7,-tol/2,-tol/2])
		//	cube([61.7,13.25+tol,h+tol]);
		// JP3
		cutout(39-3.0,43.1-7.41,2.5,7.41, above);
		// XADC J18
		cutout(dim-44.5,39.2-5,7.4,5, above);
		// Jumper JP1, mid sound
		// cutout(104.75-2.0,113,2.5,6, above); // This was way too low
		cutout(104.75-2.0,117.4,2.5,4.4, above);
		// Prog button Lower reset
		cutout(dim-34.3,84.6-4.6,4.6,4.6, above);
		// Top reset
		cutout(dim-34.3,93.8-4.6,4.6,4.6, above);
		// Jumper
		cutout(dim-50.2,84.45-2.5,9.9,2.5, above);
		// S button
		cutout(106.5-4.6,11.5-4.6,4.6,4.6, above);
		// N button
		cutout(106.5-4.6,29.5-4.6,4.6,4.6, above);
		// W button
		cutout(93,15.9,5,5, above);
		// E button
		cutout(111,15.9,5,5, above);
		// M button
		cutout(102,15.9,5,5, above);
		// Pwr and pwr switch
		cutout(0,117-16.3,14.8,16.3, above);
		// Pwr LED
		cutout(5,95.75,2.5,1.5, above);

		// Battery jumper (next to power supply)
		cutout(0,dim-11,6.5,11-7.3, above);

		// Ethernet @ 13.65
		cutout(71.37-17,dim-21.4,18,21.4, above);

		// HDMI LED
		cutout(27.35,127.4,2.5,2.0, above);

		// Network LED(s)
		// cutout(78,108.0,2.5,0.8, above);
		// cutout(78,110.9,2.5,0.8, above);
		// cutout(78,113.7,2.5,0.8, above);
		// cutout(78,108.0,2.5,6.5, above);	// This was too low
		cutout(78,110.0,2.5,7.5, above);

		//
		oledcutout();

		translate([0,0,base]) {
			// pad platform
			if (n == 0) {
				// Set up some pads to sit on the board
				// itself
				difference() {
					color("black") {
						cube([dim,dim,zh]);
					}
					translate([0,0,-zh/2]) {union() {
					nh = zh*2;

					// Across the bottom
					keepit(-1.5,-1.5,dim+1.5,5.5,nh);
					// Below the right corner
					keepit(110,0,21,9,nh);
					// Bottom right, before PMod
					keepit(dim-8,0,10,12.5,nh);

					// Right of the USBs
					keepit(6,18,8,15,nh);

					// Above the switches, below the LEDs
					keepit(20,13.25,68,3,nh);
					// Above the switches, below the LEDs
					keepit(20,20,68,3,nh);
					// Above the Bottons, on the right
					keepit(109,24,12,12,nh);
					// Left of the FMC
					keepit(108,30,12,70,nh);
					// On top of Nexys Label
					keepit(40,38,48,11,nh);
					// On top of Digilent Label
					keepit(80,58,40,19,nh);
					// On top of Xilinx Label
					keepit(14.3,89,47-14.3,12,nh);
					// Below the sound ports
					keepit(83,dim-19,99-83,8,nh);
					// Between the HDMI ports
					keepit(18.6,dim-11.5,60-18.6,13,nh);
					// Below the HDMI ports
					keepit(33,dim-19,50-33,7,nh);
					// Between USB and first left PMod
					keepit(-3,48,10,9,nh);
					// Between the two left PMods
					keepit(-2,72,12,8,nh);
					// Between right PMod and FMC
					keepit(112,23,136-112,42,nh);
					// Between FMC and PMod JXADC
					keepit(112,85,136-112,103-85,nh);
					// Between PMod JXADC and the screw
					keepit(dim-6,dim-14,10,14,nh);
					cutout(dim-12,dim-30.3,12,16,zh);
					// Left of the big yellow component
					keepit(19.5,63.5,30-19.5,67.8-63.5,nh);
					// Above the power connector
					keepit(-2,117,27.5,124-117,nh);
					// Between the sound ports
					keepit(76.5,dim-8,50,12,nh);
					}}
				}
			}

			if (n <= 1) {
				// PROG USB @ 2.4
				cutout(0,16.75-8.5,5.4,7.5,zh);
				// UART USB
				cutout(0,28.3-7.5,5.4,7.5,zh);

				// Screws
				cutout(0,0,7,7,zh);
				cutout(dim-7,0,7,7,zh);
				cutout(dim-7,dim-7,7,7,zh);
				cutout(0,dim-7,7,7,zh);

			}

			if (n <= 2) {
				// 5mm
				// Lower right PMod HA @ 4.95
				cutout(dim-12,30.6-16,12,16,zh);
				// Upper right PMod JXADC
				cutout(dim-12,dim-30.3,12,16,zh);
				// PMod JB
				cutout(0,72-16,12,16,zh);
				// PMod JC
				cutout(0,95-16,12,16,zh);
				// Large components
				cutout(29.5,61,49.5-29.5,74-61,zh);
				cutout(13.5,61,19.5-13.5,74-61,zh);
				cutout(15,
					43.5,
					5,50.3-43.5,zh);
				// Under second X in Xilinx, above FPGA
				cutout(52.7,83,61-52.7,92-83,zh);
				// Behind the Ethernet port
				cutout(66,105,73-66,5.5,zh);

			}

			if (n <= 3) {
				// 5.95mm
	
				// Sound @ 5.91
				// cutout(76.5,dim-12.2,50.1,12.2,zh);
				// Blue
				cutout( 97-7.1,dim-12.2,7.1,14,zh);
				// Pink
				cutout(107-7.1,dim-12.2,7.1,14,zh);
				// Green
				cutout(117-7.1,dim-12.2,7.1,14,zh);
				// Black
				cutout(127-7.1,dim-12.2,7.1,14,zh);
			}

			if (n <= 4) {
				// 6.6mm
				//
				// FMC connector @ 6.55
				cutout(dim-14.75,96.4-57.5,14.8,57.5,zh);
			}

			if (n <= 5) {
				// 7mm
				// Big USB, lower left @ 6.9
				cutout(0,48.6-13.4,14.6,13.4,zh);
			}

			if (n <= 6) {
				// 7.8mm
				// HDMI in @ 7.6
				cutout(8.4,dim-11.64,15.1,11.64,zh);
				// HDMI out
				cutout(33.3,dim-11.64,15.1,11.64,zh);
				// Display port out @ 7.5mm above board surface
				cutout(85.45-8.8,122,8.9,15, zh);
			}
		}
	}

	module  embossZip() {
		s = 0.8;
		depth = 1.5;
		translate([56/2, 57, height+zlogoh/2-depth]) {
			rotate([0,0,0]) scale([s,s,1]) {
				translate([-zlogow/2,(zlogob-zlogol)/2,
							-zlogoh/2])
						zipcpulogo();
			}
		}
	}

	module  embossVZip() {
		s = 1.6;
		depth = 1.5;
		translate([37, 80, height+vzlogoh/2-depth]) {
			rotate([0,0,0]) scale([s,s,1]) {
				translate([-vzlogow/2,(vzlogob-vzlogol)/2,
							-vzlogoh/2])
						vziplogo();
			}
		}
	}

	module  embossGT() {
		s = 1.6;
		depth = 1.5;
		translate([110, 58, height+gtlogo_h/2-depth]) {
			rotate([0,0,0]) scale([s,s,1]) {
				translate([-gtlogo_w/2,(-gtlogo_l)/2,
							-gtlogo_h/2])
						GTlogo();
			}
		}
	}

	difference() {
		cube([dim,dim,height]);
		layer(0);
		layer(1);
		layer(2);
		layer(3);
		layer(4);
		layer(5);
		layer(6);
		layer(7);
		embossZip();
		embossGT();
		embossVZip();
		//
		// oledcutout();
	}
}

rotate([180,0,0]) { translate([0,-152,-10]) {
	if(1) {
	intersection() {
		translate([-10,-10,-20])
			cube([155,10+72,50]);
		videozip();
	}}

	if (0) { translate([0,5,0]) {
		intersection() {
			translate([-10,36,-20])
				cube([155,36,50]);
			videozip();
		}
	}}

	if (1) { translate([0,10,0]) {
		intersection() {
			translate([-10,72,-20])
				cube([155,80,50]);
			videozip();
		}
	}}

	if (0) { translate([0,15,0]) {
		intersection() {
			translate([-10,108,-20])
				cube([155,36+20,50]);
			videozip();
		}
	}}
}}

