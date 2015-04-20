component simple {
	intField1 : int<0..100> = 0;
		
	fault faultTransient {
			step {
				choice {
					true => { faultTransient := false;}
					true => { faultTransient := true;}
				}
			}
		}
	
	rport1 ( inout inout_r : int);
	
	[faultTransient]
	pport1 (inout inout_p : int) {
		inout_p := intField1 + 0;
	}
	
	pport1 (inout inout_p : int) {
		inout_p := intField1 + 1;
	}
	
	simple.rport1 = delayed simple.pport1
	
	
	step {
		int intLocal1;
		step faultTransient;
		rport1(inout intLocal1);
		intField1 := intLocal1;
	}
}
