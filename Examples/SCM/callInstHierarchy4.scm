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
		
	rport1 = instantly nested.pport1
	
	step {
		locals{}
		rport1 ( );
		step nested;
	}
}
