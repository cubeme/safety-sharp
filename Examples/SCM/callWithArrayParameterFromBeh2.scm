component simple {
	intArrayField : Array<2,int<0..100>> = [1;2];
	
	rport1 ( inout r_inout : Array<_,int>> );
	
	pport1 ( inout p_inout : Array<_,int>> ) {
		foreach i in p_input { p_inout := p_inout + 1; } ;
	}
	
	simple.rport1 = instantly simple.pport1 
	
	step {
		rport1 (inout intArrayField);
	}
}
