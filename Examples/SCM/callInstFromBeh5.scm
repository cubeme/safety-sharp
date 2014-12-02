component simple {
	intField = 1;
	
	rport1 ( inout r_inout  : int )
	
	pport1 ( inout p_inout  : int ) {
		locals{
		}
		p_inout := 5;
	}
	
	rport1 = instantly pport1 
	
	step {
		locals{
		}
		rport1 (inout intField)
	}
}
