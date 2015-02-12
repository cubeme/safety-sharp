component simple {	
	component nested {
		intField : int = 0;
		
		pport1 ( ) {
			locals{
			}
			intField := 1;
		}	
		
		step { locals{} }
	}
	
	rport1 ( );
		
	simple.rport1 = instantly simple.nested.pport1
	
	step {
		locals{}
		rport1 ( );
		step nested;
	}
}
