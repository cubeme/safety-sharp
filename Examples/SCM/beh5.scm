component simple {	
	boolField1 : bool = false;
	intArrayField1 : Array<3,int<0..100>> = [0;0;0];
	
	intArrayField1_0 : int<0..100> = 0;
	intArrayField1_1 : int<0..100> = 0;
	intArrayField1_2 : int<0..100> = 0;
	
	rport_IntArray ( );
	
	pport_IntArray () {				
		int intLocal0;
		int intLocal1;
		int intLocal2;
		intLocal0 := 0;
		intLocal1 := 1;
		intLocal2 := 2;
		boolField1 := intArrayField1[intLocal0] || intArrayField1[intLocal1] || intArrayField1[intLocal2];
	}
		
	pport_BoolArrayFlattened () {		
		int intLocal0;
		int intLocal1;
		int intLocal2;
		intLocal0 := 0;
		intLocal1 := 1;
		intLocal2 := 2;
		
		boolField1 :=
			( intLocal0==0 ? intArrayField1_0 : ( intLocal0==1 ? intArrayField1_1 : intArrayField1_2 ) ) ||
			( intLocal1==0 ? intArrayField1_0 : ( intLocal1==1 ? intArrayField1_1 : intArrayField1_2 ) ) ||
			( intLocal2==0 ? intArrayField1_0 : ( intLocal2==1 ? intArrayField1_1 : intArrayField1_2 ) );
	}
	
	simple.rport_IntArray = instantly simple.pport_IntArray
	
	step {
		rport_IntArray ( );
	}
}


