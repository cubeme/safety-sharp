component simple {
	rport1 ( );
	
	pport1 ( ) {
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		rport1 ();		
	}
}
