component simple {
	component nested {
		intField : int<0..100> = 0;
		
		rport1 ( );
		
		pport1 ( ) {
			intField := 1;
		}
		
		step {
			rport1 ( );
		}
	}
	
	simple.nested.rport1 = instantly simple.nested.pport1
	
	step {
		step nested;
	}
}
