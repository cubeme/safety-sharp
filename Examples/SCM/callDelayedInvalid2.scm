component simple {
	intField1 : int = 0;
	
	rport1 ( inputInt : int, inout inout_r : int);

	pport1 ( inputInt : int, inout inout_p : int) {
		locals{
		}
		intField1 := intField1 + 1;
	}	
	
	
	simple.rport1 = delayed simple.pport1
	
	
	step {
		locals{
			int intLocal1;
		}
		rport1(3+7, inout intLocal1);
		intField1 := intLocal1;
	}
}
