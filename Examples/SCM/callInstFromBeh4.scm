component simple {
	intField : int<0..100> = 1;
	
	rport1 ( in r_input1:int, in r_input2:int );
	
	pport1 ( in p_input1:int, in p_input2:int ) {
		intField := intField + p_input1 + p_input2;		
	}
	
	simple.rport1 = instantly simple.pport1 
	
	step {		
		int intLocal;
		intLocal := 4 ;
		rport1 ( in 5 + 7, in intLocal);
	}
}
