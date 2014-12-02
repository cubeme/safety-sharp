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
	
	rport1 = instantly pport1 
	rport2 = instantly pport2
	
	step {
		locals{
		}
		rport1 ( )
		
	}
}
