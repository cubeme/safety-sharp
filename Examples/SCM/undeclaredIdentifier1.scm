component simple {
	
	pport1 ( inout inout1 : int ) {
		locals{}
	}

	pport2 ( inout inout2 : int  ) {
		locals{}
		inout1 :=5;
	}
	
	
	step {
		locals{}
	}
}
