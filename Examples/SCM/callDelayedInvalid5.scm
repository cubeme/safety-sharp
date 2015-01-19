component simple {
	intField1 : int = 0;
		
	rport1 ( inout inout_r : int);
	rport2 ( inout inout_r : int);
	
	pport1 (inout inout_p : int) {
		locals{
		}
		rport2(inout_p);
	}
	
	pport2 (inout inout_p : int) {
		locals{
		}
		intField1 := intField1 + 1;
		inout_p := intField1;
	}	
	
	
	rport1 = delayed pport1
	rport2 = instantly pport2
	
	
	step {
		locals{
			int intLocal1;
		}
		rport1(intLocal1);
	}
}
