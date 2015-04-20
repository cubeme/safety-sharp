component simple {
	rport1 ( in a1:int, in a2:int, inout b:bool);
	rport2 ( in a1:int, in a2:int, inout b:bool);
	
	pport1 ( in a1:int, in a2:int, inout b:bool) {
	}
	
	simple.rport1 = instantly simple.pport1
	simple.rport2 = delayed simple.pport1
	
	step {
	}
}
