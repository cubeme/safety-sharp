component simple {
	component nestedRequired {
		component nested2Required {
			component nested3Required {
				rport1 ( );
				step {
					rport1 ( );
				}
			}
			step {
				step nested3Required;
			}			
		}		
		step {
			step nested2Required;
		}
	}
	
	intField : int<0..100> = 0;
	
	pport1 ( ) {
		intField := 1;
	}
		
	simple.nestedRequired.nested2Required.nested3Required.rport1 = instantly simple.pport1
	
	step {
		step nestedRequired;
	}
}
