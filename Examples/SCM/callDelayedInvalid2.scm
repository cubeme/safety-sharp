component simple {
	intField1 : int = 0;
	
	rport1 ( in inputInt:int, inout inout_r:int);

	pport1 ( in inputInt:int, inout inout_p:int) {
		intField1 := intField1 + 1;
	}	
	
	
	simple.rport1 = delayed simple.pport1
	
	
	step {
		int intLocal1;
		rport1( in 3+7, inout intLocal1);
		intField1 := intLocal1;
	}
}
