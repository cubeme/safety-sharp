component simple {
	rport1 ( );
	
	pport1 ( ) {
		locals{
		}
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		rport1 ();		
	}
}
