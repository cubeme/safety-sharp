component simple {	
	intBoolArray1 : Array<3,int<0..100>> = [0;0;0];
	
	intBoolArray1_0 : int<0..100> = 0;
	intBoolArray1_1 : int<0..100> = 0;
	intBoolArray1_2 : int<0..100> = 0;
	
	rport_BoolArray ( );
	
	pport_BoolArray () {		
		boolField1 := intBoolArray1[intLocal0] || intBoolArray1[intLocal1] || intBoolArray1[intLocal2];
	}
		
	pport_BoolArrayFlattened () {		
		int intLocal0;
		int intLocal1;
		int intLocal2;
		
		boolField1 :=
			( intLocal0==0 ? intBoolArray1_0 : ( intLocal0==1 ? intBoolArray1_1 : intBoolArray1_2 ) ) ||
			( intLocal1==0 ? intBoolArray1_0 : ( intLocal1==1 ? intBoolArray1_1 : intBoolArray1_2 ) ) ||
			( intLocal2==0 ? intBoolArray1_0 : ( intLocal2==1 ? intBoolArray1_1 : intBoolArray1_2 ) );
	}
	
	simple.rport_BoolArray = instantly simple.pport_BoolArray
	
	step {
		rport_BoolArray ( );
	}
}


