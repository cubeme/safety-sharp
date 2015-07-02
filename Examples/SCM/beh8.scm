component simple {	
	int intField1 : int<0..100> = 0;
		
	intArrayInArrayField1 : Array<2,int<0..100>> = [0;1];
	
	rport_intIncrease (inout r_inout  : int);
	
	pport_intIncrease (inout r_inout  : int) {
		r_inout := r_inout + 1;
	}
	
	simple.rport_intIncrease = instantly simple.pport_intIncrease
	
	step {
		foreach i in boolArrayInArrayField1 {
			rport_intIncrease (i);
		}
	}
}


