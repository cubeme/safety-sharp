component simple {
	intField1 : int<0..100> = 0;
		
	rport1 ( inout inout_r : int);
	rport2 ( inout inout_r : int);
	
	pport1 (inout inout_p : int) {
		rport2(inout inout_p);
	}
	
	pport2 (inout inout_p : int) {
		inout_p := intField1 + 1;
	}	
	
	
	simple.rport1 = delayed simple.pport1
	simple.rport2 = delayed simple.pport2
	
	
	step {
		int intLocal1;
		rport1(inout intLocal1);
		intField1 := intLocal1;
	}
}
