component simple {	
	component nestedProvided {
		intField : int<0..100> = 0;
		
		pport1 ( ) {
			intField := 1;
		}	
		
		step {
		}
	}
	
	component nestedRequired {
		rport1 ( );
		
		step {
			rport1 ( );
		}
	}
		
	simple.nestedRequired.rport1 = instantly simple.nestedProvided.pport1
	
	step {
		step nestedRequired;
	}
}
