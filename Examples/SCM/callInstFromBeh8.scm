component simple {
	rport1 ( inout r_inout  : int );
	
	pport1 ( inout p_inout  : int ) {
		locals{
		}
		p_inout := 1;
	}
	
	simple.rport1 = instantly simple.pport1 
	
	step {
		locals{
			int intLocal;
		}
		rport1 (  inout intLocal );
	}
}
