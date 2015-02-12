component simple {
	intField : int = 1;
	
	fault faultTransient1 {
			step {
				locals{}
				choice {
					true => { faultTransient1 := false;}
					true => { faultTransient1 := true;}
				}
			}
		}
	fault faultTransient2 {
			step {
				locals{}
				choice {
					true => { faultTransient2 := false;}
					true => { faultTransient2 := true;}
				}
			}
		}
	
	rport1 ( );
	
	[faultTransient1]
	pport1 ( ) {
		locals {
		}
	}
	
	pport1 ( ) {
		locals {
		}
		intField := intField + 3;
	}
	
	simple.rport1 = instantly simple.pport1
	
	[faultTransient2]
	step {
		locals{
		}
		step faultTransient2;
	}
	
	step {
		locals{
		}
		rport1 ();
		step faultTransient1;
		step faultTransient2;
	}
}