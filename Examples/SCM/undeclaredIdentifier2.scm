component simple {
	
	rport1 ( inout inout1 : int )

	pport1 ( inout inout2 : int  ) {
		locals{}
		inout1 :=5;
	}
	
	
	step {
		locals{}
	}
}
