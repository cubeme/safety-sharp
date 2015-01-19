component simple {
	intField1 : int = 0;
	
	rport1 ( inout inout_r : int);

	pport1 (  inout inout_p : int) {
		locals{
		}
		inout_p := inout_p + 1;
	}	
	
	
	rport1 = delayed pport1
	
	
	step {
		locals{
			int intLocal1;
		}
		intLocal1 := 1;
		rport1(inout intLocal1);
		intField1 := intLocal1;
	}
}
