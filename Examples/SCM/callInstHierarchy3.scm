component simple {	
	component nested {		
		rport1 ( );
			
		step {
			locals{
			}
			rport1 ( );
		}
	}
	intField : int = 0;
	
	pport1 ( ) {
		locals{
		}
		intField := 1;
	}
	
	simple.nested.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		step nested;
	}
}
