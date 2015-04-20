component simple {
	intField : int<0..100> = 1 ;
	
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
	rport2 ( inout r_inout  : int );
	
	pport1 ( ) {
		int intLocal;
		intLocal := 3 ;
		rport2 ( inout intLocal ) ;
		intField := intLocal;
	}
	
	[faultTransient1]
	pport2 ( inout p_inout  : int ) {
	}
	
	pport2 ( inout p_inout  : int ) {
		p_inout := p_inout + 1;
	}
	
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
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
