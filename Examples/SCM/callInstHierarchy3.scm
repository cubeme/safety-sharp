component simple {	
	component nested {		
		rport1 ( );
			
		step {
			rport1 ( );
		}
	}
	intField : int<0..100> = 0;
	
	pport1 ( ) {
		intField := 1;
	}
	
	simple.nested.rport1 = instantly simple.pport1
	
	step {
		step nested;
	}
}
