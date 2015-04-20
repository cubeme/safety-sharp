component simple {
	intField1 : int<0..100> = 0;
	
	rport1 ( );

	pport1 ( )  {
		intField1 := intField1 + 1;
	}	
		
	simple.rport1 = delayed simple.pport1
	
	
	step {
		rport1();
	}
}
