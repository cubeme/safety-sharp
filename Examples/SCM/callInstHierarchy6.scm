component simple {	
	component nested {
		intField : int<0..100> = 0;
		
		rport1 ( );
		
		pport1 ( ) {
			intField := 1;
		}	
		
		nested.rport1 = instantly nested.pport1
		
		step {
			rport1 ( );
		}
	}
	
	
	step {
		step nested;
	}
}
