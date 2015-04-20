component simple {
	intField : int<0..100> = 1;
	
	fault faultTransient1 {
			step {
				choice {
					true => { faultTransient1 := false;}
					true => { faultTransient1 := true;}
				}
			}
		}
	fault faultTransient2 {
			step {
				choice {
					true => { faultTransient2 := false;}
					true => { faultTransient2 := true;}
				}
			}
		}
	
	rport1 ( );
	
	[faultTransient1]
	pport1 ( ) {
	}
	
	pport1 ( ) {
		intField := intField + 3;
	}
	
	simple.rport1 = instantly simple.pport1
	
	[faultTransient2]
	step {
		step faultTransient2;
	}
	
	step {
		rport1 ();
		step faultTransient1;
		step faultTransient2;
	}
}