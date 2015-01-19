component simple {
	intField1 : int = 0;
		
	fault faultTransient {
			step {
				locals{}
				choice {
					true => { faultTransient := false;}
					true => { faultTransient := true;}
				}
			}
		}
	
	rport1 ( inout inout_r : int);
	
	[faultTransient]
	pport1 (inout inout_p : int) {
		locals{
		}
		inout_p := intField1 + 0;
	}
	
	pport1 (inout inout_p : int) {
		locals{
		}
		inout_p := intField1 + 1;
	}
	
	rport1 = delayed pport1
	
	
	step {
		locals{
			int intLocal1;
		}
		step faultTransient;
		pport1(intLocal1);
		intField1 := intLocal1;
	}
}
