component simple {	
	component nested {
		intField_inner : int = 0;
		
		rport_Increase ( );
		rport_GetOldFieldValue ( inout inout_p : int );
		
		pport_Increase () {
			locals{
			}
			intField_inner := intField_inner + 1;
		}
		
		pport_GetFieldValue (inout inout_p : int) {
			locals{
			}
			inout_p := intField_inner;
		}	
		
		pport_FromExtern (inout inout_p : int) {
			locals{
			}
			rport_GetOldFieldValue (inout_p ) ;
		}	
		
		nested.rport_Increase = instantly nested.pport_Increase
		nested.rport_GetOldFieldValue = delayed nested.pport_GetFieldValue
		
		step {
			locals{
			}
			rport_Increase ( );
		}
	}
	
	intField_outer : int = 0;
	
	rport_increaseAfterNestedStep ( );
	rport_getValue ( inout intField_outer : int);
	
	simple.rport_increaseAfterNestedStep = instantly simple.nested.pport_Increase
	simple.rport_getValue = instantly simple.nested.pport_FromExtern
	
	step {
		locals{
		}
		step nested;
		rport_getValue( inout intField_outer );
		rport_increaseAfterNestedStep( );
	}
}
