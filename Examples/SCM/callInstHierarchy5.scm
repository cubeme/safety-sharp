component simple {	
	component nestedProvided {
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
	
	component nestedRequired {
		rport1 ( );
		
		step {
			locals{}
			rport1 ( );
		}
	}
		
	nestedRequired.rport1 = instantly nestedProvided.pport1
	
	step {
		locals{
		}
		step nestedRequired;
	}
}
