component simple {
	intField : int<0..100> = 1;
		
	pport1 ( ) {
		intField := intField + 3;
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		rport1 ( );
		
	}
}
