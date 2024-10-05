#include <stdio.h>
#include <stdlib.h>

unsigned	syndrome(unsigned long v) {
	const	unsigned	POLY = 0xc1;
	unsigned	f = 0, b;

	for(int k=0; k<64; k++) {
		b = (v >> (63-k))&1;
		b ^= (f >> 7)&1;
		if (b)
			f = (f<<1) ^ POLY;
		else
			f <<= 1;
	} return f & 0x0ff;
}

unsigned long	remix(unsigned long v) {
	unsigned long	nv;

	nv = 0ul;
	for(int k=0; k<28; k++) {
		if (v & (1ul<<(55-(2*k))))
			nv |= (1ul << (55-k));
		if (v & (1ul<<(54-(2*k))))
			nv |= (1ul << (27-k));
	} return nv;
}

int main(int argc, char **argv) {
	unsigned long	dec64[256], dec32[256];
	unsigned	ij, ik, s;
	FILE		*fp;

	for(ij=0; ij<256; ij++)
		dec64[ij] = 0;

	for(ij=0; ij<63; ij=ij+1) {
		for(ik=ij+1; ik<64; ik++) {
			unsigned long	v;
			unsigned	s;

			v  = (1ul << ij);
			v |= (1ul << ik);
			s = syndrome(v);
			// printf("S[%2d,%2d] -> %02x\n", ij, ik, s);
			dec64[s] = remix(v);
		}
	}

	for(ij=0; ij<64; ij=ij+1) {
		unsigned long	v;
		unsigned	s;

		v = (1ul << ij);
		s = syndrome(v);
		// printf("S[%2d   ] -> %02x\n", ij, s);
		dec64[s] = remix(v);
	}

	dec64[0] = 0;

	fp = fopen("bchdec64.hex", "w");
	for(ij=0; ij<256; ij++)
		fprintf(fp, "%014lx\n", dec64[ij]);
	fclose(fp);

	for(ij=0; ij<256; ij++)
		dec32[ij] = 0;

	for(ij=0; ij<31; ij=ij+1) {
		for(ik=ij+1; ik<32; ik++) {
			unsigned long	v;
			unsigned	s;

			v  = (1ul << ij);
			v |= (1ul << ik);
			s = syndrome(v);
			dec32[s] = v >> 8;
		}
	}

	for(ij=0; ij<32; ij=ij+1) {
		unsigned long	v;
		unsigned	s;

		v = (1ul << ij);
		s = syndrome(v);
		dec32[s] = v >> 8;
	}

	fp = fopen("bchdec32.hex", "w");
	for(ij=0; ij<256; ij++)
		fprintf(fp, "%06lx\n", dec32[ij]);
	fclose(fp);
}
