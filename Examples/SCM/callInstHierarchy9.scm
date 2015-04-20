component simple {
	component nested {
		component nested2Required {
			component nested3Required {
				rport1 ( );
				step {
					rport1 ( );
				}
			}
			step {
				step nested3Required;
			}			
		}
		intField : int<0..100> = 0;
	
		pport1 ( ) {
			intField := 1;
		}		
		
		nested.nested2Required.nested3Required.rport1 = instantly nested.pport1
		
		step {
			step nested2Required;
		}
		
	}
	
	step {
		step nested;
	}
}
