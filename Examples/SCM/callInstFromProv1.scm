component simple {
	intField : int = 1 ;
	
	rport1 ( );
	rport2 ( inout r_inout  : int );
	
	pport1 ( ) {
		locals{
			int intLocal;
		}
		intLocal := 3 ;
		rport2 ( inout intLocal ) ;
		intField := intLocal;
	}
	
	pport2 ( inout p_inout  : int ) {
		locals{
		}
		p_inout := p_inout + 1;
	}
	
	rport1 = instantly pport1 
	rport2 = instantly pport2
	
	step {
		locals{
		}
		rport1 ();
	}
}
