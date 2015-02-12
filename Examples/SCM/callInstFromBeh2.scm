component simple {
	rport1 ( );
	rport2 ( );
	
	pport1 ( ) {
		locals{
		}
		rport2 ( );
	}
	
	pport2 ( ) {
		locals{
		}
	}
	
	simple.rport1 = instantly simple.pport1 
	simple.rport2 = instantly simple.pport2
	
	step {
		locals{
		}
		rport1 ( );
		
	}
}
