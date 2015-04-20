component simple {
	rport1 ( );
	rport2 ( );
	
	pport1 ( ) {
		rport2 ( );
	}
	
	pport2 ( ) {
	}
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
	step {
		rport1 ( );
		
	}
}
