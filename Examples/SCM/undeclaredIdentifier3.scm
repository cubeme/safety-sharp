component simple {
	component nested {
		rport1 ( inout inout1 : int )
		step {
		}
	}
	pport1 ( inout inout2 : int  ) {
		inout1 :=5;
	}
		
	step {
	}
}
