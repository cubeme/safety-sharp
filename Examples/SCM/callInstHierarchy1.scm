component simple {
	intField : int<0..100> = 0;
	
	rport1 ( );
	
	pport1 ( ) {
		intField := 1;
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		rport1 ( );
		
	}
}
