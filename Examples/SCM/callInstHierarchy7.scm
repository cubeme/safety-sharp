component simple {	
	component nestedProvided {
		component nested2Provided {
			intField : int<0..100> = 0;
			
			pport1 ( ) {
				intField := 1;
			}
			step {
			}
		}
		step {
		}
	}
	
	component nestedRequired {
		component nested2Required {
			rport1 ( );
			step {
				rport1 ( );
			}
		}
		
		step {
			step nested2Required;
		}
	}
		
	simple.nestedRequired.nested2Required.rport1 = instantly simple.nestedProvided.nested2Provided.pport1
	
	step {
		step nestedRequired;
	}
}
