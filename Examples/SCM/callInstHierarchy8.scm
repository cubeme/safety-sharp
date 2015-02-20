component simple {
	component nestedRequired {
		component nested2Required {
			component nested3Required {
				rport1 ( );
				step {
					locals{}
					rport1 ( );
				}
			}
			step {
				locals{}
				step nested3Required;
			}			
		}		
		step {
			locals{}
			step nested2Required;
		}
	}
	
	intField : int = 0;
	
	pport1 ( ) {
		locals{
		}
		intField := 1;
	}
		
	simple.nestedRequired.nested2Required.nested3Required.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		step nestedRequired;
	}
}
