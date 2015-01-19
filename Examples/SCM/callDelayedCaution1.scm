component simple {	
	component nested {
		intField_inner : int = 1;
		
		rport1 ( inout inout_r : int);
		
		pport1 (inout inout_p : int) {
			locals{
			}
			intField_inner := intField_inner + 1;
		}	
		
		pport2 (inout inout_p : int) {
			locals{
			}
			inout_p := intField_inner;
		}	
		
		rport1 = delayed pport1
		
		step {
			locals{
			}
			rport1 ( );
		}
	}
	
	intField_outer : int = 0;
	
	rport_toCallFirst ( inout inout_r : int);
	
	rport_toCallFirst = instantly nested.pport2
	
	step {
		locals{
		}
		rport_toCallFirst( intField_outer );
		step nested;
	}
}
