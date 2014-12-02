component simple {
	component nested {
		intField : int = 0;
		
		rport1 ( )
		
		pport1 ( ) {
			locals{
			}
			intField := 1;
		}
		
		step {
			locals{
			}
			rport1 ( )
		}
	}
	
	nested.rport1 = instantly nested.pport1
	
	step {
		locals{
		}
		step nested;
	}
}
