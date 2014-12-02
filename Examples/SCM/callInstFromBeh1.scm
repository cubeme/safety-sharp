component simple {
	rport1 ( );
	
	pport1 ( ) {
		locals{
		}
	}
	
	rport1 = instantly pport1
	
	step {
		locals{
		}
		rport1 ();		
	}
}
