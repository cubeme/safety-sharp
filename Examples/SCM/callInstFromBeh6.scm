component simple {

	rport1 ( inout r_inout  : int )
	
	pport1 ( inout p_inout  : int ) {
		locals{
		}
		p_inout := p_inout + 1;
	}
	
	rport1 = instantly pport1 
	
	step {		
		locals{
			int intLocal;
		}
		intLocal := 4 ;
		rport1 (  inout intLocal )
	}
}
