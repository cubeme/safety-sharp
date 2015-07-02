component simple {

	rport1 ( inout r_inout : Array<_,int>> );
	
	pport1 ( inout p_inout : Array<_,int>> ) {
	}
	
	simple.rport1 = instantly simple.pport1 
	
	step {		
		intArrayLocal : Array<2,int> ;
		rport1 ( inout intArrayLocal );
	}
}
