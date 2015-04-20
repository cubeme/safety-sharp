component simple {
	intField : int<0..100> = 1 ;
	
	rport1 ( );
	rport2 ( inout r_inout  : int );
	
	pport1 ( ) {
		int intLocal;
		intLocal := 3 ;
		rport2 ( inout intLocal ) ;
		intField := intLocal;
	}
	
	pport2 ( inout p_inout  : int ) {
		p_inout := p_inout + 1;
	}
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
	step {
		rport1 ();
	}
}
