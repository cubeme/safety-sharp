component simple {
	rport1 ( a1 : int, a2 : int, inout b:bool);
	rport2 ( a1 : int, a2 : int, inout b:bool);
	
	pport1 ( a1 : int, a2 : int, inout b:bool) {
		locals{}
	}
	
	simple.rport1 = instantly simple.pport1
	simple.rport2 = delayed simple.pport1
	
	step {
		locals{}
	}
}
