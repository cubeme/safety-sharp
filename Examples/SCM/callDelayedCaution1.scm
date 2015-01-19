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
		
		rport_Increase = instantly pport_Increase
		rport_GetOldFieldValue = delayed pport_GetFieldValue
		
		step {
			locals{
			}
			rport_Increase ( );
		}
	}
	
	intField_outer : int = 0;
	
	rport_increaseBeforeNestedStep ( );
	rport_getValue ( inout intField_outer : int);
	
	rport_increaseBeforeNestedStep = instantly nested.pport_Increase
	rport_getValue = instantly nested.pport_FromExtern
	
	step {
		locals{
		}
		rport_increaseBeforeNestedStep( );
		step nested;
		rport_getValue( inout intField_outer );
	}
}
