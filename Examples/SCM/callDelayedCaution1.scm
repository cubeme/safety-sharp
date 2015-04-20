component simple {	
	component nested {
		intField_inner : int<0..100> = 0;
		
		rport_Increase ( );
		rport_GetOldFieldValue ( inout inout_p : int );
		
		pport_Increase () {
			intField_inner := intField_inner + 1;
		}
		
		pport_GetFieldValue (inout inout_p : int) {
			inout_p := intField_inner;
		}	
		
		pport_FromExtern (inout inout_p : int) {
			rport_GetOldFieldValue (in inout_p ) ;
		}	
		
		nested.rport_Increase = instantly nested.pport_Increase
		nested.rport_GetOldFieldValue = delayed nested.pport_GetFieldValue
		
		step {
			rport_Increase ( );
		}
	}
	
	intField_outer : int<0..100> = 0;
	
	rport_increaseBeforeNestedStep ( );
	rport_getValue ( inout intField_outer : int);
	
	simple.rport_increaseBeforeNestedStep = instantly simple.nested.pport_Increase
	simple.rport_getValue = instantly simple.nested.pport_FromExtern
	
	step {
		rport_increaseBeforeNestedStep( );
		step nested;
		rport_getValue( inout intField_outer );
	}
}
