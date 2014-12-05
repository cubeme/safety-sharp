component simple {
	intField : int = 0;
	
	rport1 ( );
	
	pport1 ( ) {
		locals{
		}
		intField := 1;
	}
	
	rport1 = instantly pport1
	
	step {
		locals{
		}
		rport1 ( );
		
	}
}
