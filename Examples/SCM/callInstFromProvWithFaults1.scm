component simple {
	intField : int = 1 ;
	
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
	rport2 ( inout r_inout  : int );
	
	pport1 ( ) {
		locals{
			int intLocal;
		}
		intLocal := 3 ;
		rport2 ( inout intLocal ) ;
		intField := intLocal;
	}
	
	[faultTransient1]
	pport2 ( inout p_inout  : int ) {
		locals{
		}
	}
	
	pport2 ( inout p_inout  : int ) {
		locals{
		}
		p_inout := p_inout + 1;
	}
	
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
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
