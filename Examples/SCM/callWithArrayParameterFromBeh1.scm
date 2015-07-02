component simple {
	intArrayField : Array<2,int<0..100>> = [1;2];
	intField : int<0..100> = 0;
	
	rport1 ( in r_input:Array<_,int>);
	
	pport1 ( in p_input:Array<_,int>> ) {
		foreach i in p_input { intField := intField + i; } ;
	}
	
	rport2 ( in r_input:Array<_,int>);
	
	pport2 ( in p_input:Array<2,int>> ) {
		//size of input array must be known here, because the indexes 0,1 are used explicitely in the body
		intArrayField[0] := intArrayField[0] + p_input[0];
		intArrayField[1] := intArrayField[1] + p_input[1];
	}
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2 
	
	step {		
		Array<2,int>> intArrayLocal ;
		intArrayLocal[0] := 4 ;
		intArrayLocal[1] := 5 ;
		rport1 ( in intArrayLocal);
		rport2 ( in intArrayLocal);
	}
}
