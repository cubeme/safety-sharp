component simple {
	rport1 ( a1 : int, a2 : int, inout b:bool);
	rport2 ( a1 : int, a2 : int, inout b:bool);
	
	pport1 ( a1 : int, a2 : int, inout b:bool) {
		locals{}
	}
	
	rport1 = instantly pport1
	rport2 = delayed pport1
	
	step {
		locals{}
	}
}
