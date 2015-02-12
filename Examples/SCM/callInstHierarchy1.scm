component simple {
	intField : int = 0;
	
	rport1 ( );
	
	pport1 ( ) {
		locals{
		}
		intField := 1;
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		rport1 ( );
		
	}
}
