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
	
	nested.rport1 = instantly pport1
	
	step {
		locals{
		}
		step nested;
	}
}
