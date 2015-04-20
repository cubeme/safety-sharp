component simple {

	rport1 ( inout r_inout  : int );
	
	pport1 ( inout p_inout  : int ) {
	}
	
	simple.rport1 = instantly simple.pport1 
	
	step {		
		int intLocal;
		rport1 (  inout intLocal );
	}
}
