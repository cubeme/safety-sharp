component simple {
	component nested {
		rport1 ( inout inout1 : int )
		step {
			locals{}
		}
	}
	pport1 ( inout inout2 : int  ) {
		locals{}
		inout1 :=5;
	}
	
	
	step {
		locals{}
	}
}
