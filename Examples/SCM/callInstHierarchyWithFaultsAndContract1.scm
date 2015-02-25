component simple {
	component nested {
		intField : int = 0;
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
		
		[faultTransient2]
		pport1 ( )
			ensures (nested.intField==nested.intField⁻) changes intField
		{
			locals{
			}
		}
		
		pport1 ( )
			ensures nested.intField==1 changes intField
		{
			locals{
			}
			intField := 1;
		}
		
		step {
			locals{
			}
			step faultTransient2;
			rport1 ( );
		}
	}
	
	fault faultTransient1 {
			step {
				locals{}
				choice {
					true => { faultTransient1 := false;}
					true => { faultTransient1 := true;}
				}
			}
		}
	simple.nested.rport1 = instantly simple.nested.pport1
	
	[faultTransient1]
	step {
		locals{
		}
	}
	
	step
			ensures simple.nested.intField==1
		{
		locals{
		}
		step nested;
		step faultTransient1;		
	}
}
