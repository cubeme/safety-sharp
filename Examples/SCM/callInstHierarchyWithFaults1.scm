component simple {
	component nested {
		intField : int<0..100> = 0;
		fault faultTransient2 {
				step {
					choice {
						true => { faultTransient2 := false;}
						true => { faultTransient2 := true;}
					}
				}
			}
		
		rport1 ( );
		
		[faultTransient2]
		pport1 ( ) {
		}
		
		pport1 ( ) {
			intField := 1;
		}
		
		step {
			step faultTransient2;
			rport1 ( );
		}
	}
	
	fault faultTransient1 {
			step {
				choice {
					true => { faultTransient1 := false;}
					true => { faultTransient1 := true;}
				}
			}
		}
	simple.nested.rport1 = instantly simple.nested.pport1
	
	[faultTransient1]
	step {
	}
	
	step {
		step nested;
		step faultTransient1;		
	}
}
