component simple {
	intArrayField : Array<2,int<0..100>> = [1;2];
	
	rport1 ( );
	rport2 ( inout r_inout  : Array<_,int>> );
	
	pport1 ( ) {
		Array<2,int> intArrayLocal;
		intArrayLocal[0] := 3 ;
		intArrayLocal[1] := 4 ;
		rport2 ( inout intArrayLocal ) ;
		foreach i,j in intArrayField,intArrayLocal { i := j; }; //maybe abbreviate to intArrayField := intArrayLocal;
	}
	
	pport2 ( inout p_inout  : Array<_,int>> ) {
		foreach i in p_inout { i := i + 1; }
	}
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
	step {
		rport1 ();
	}
}
