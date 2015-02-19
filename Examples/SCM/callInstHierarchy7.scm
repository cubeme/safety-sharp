component simple {	
	component nestedProvided {
		component nested2Provided {
			intField : int = 0;
			
			pport1 ( ) {
				locals{
				}
				intField := 1;
			}
			step {
				locals{
				}
			}
		}
		step {
			locals{
			}
		}
	}
	
	component nestedRequired {
		component nested2Required {
			rport1 ( );
			step {
				locals{}
				rport1 ( );
			}
		}
		
		step {
			locals{}
			step nested2Required;
		}
	}
		
	simple.nestedRequired.nested2Required.rport1 = instantly simple.nestedProvided.nested2Provided.pport1
	
	step {
		locals{
		}
		step nestedRequired;
	}
}
