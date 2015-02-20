component simple {
	component nested {
		component nested2Required {
			component nested3Required {
				rport1 ( );
				step {
					locals{}
					rport1 ( );
				}
			}
			step {
				locals{}
				step nested3Required;
			}			
		}
		intField : int = 0;
	
		pport1 ( ) {
			locals{
			}
			intField := 1;
		}		
		
		nested.nested2Required.nested3Required.rport1 = instantly nested.pport1
		
		step {
			locals{}
			step nested2Required;
		}
		
	}
	
	step {
		locals{
		}
		step nested;
	}
}
