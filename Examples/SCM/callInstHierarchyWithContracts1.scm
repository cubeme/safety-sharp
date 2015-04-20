component simple {
	component nested {
		intField : int<0..100> = 0;
		
		rport1 ( );
		
		pport1 ( )
			ensures nested.intField==1 changes intField
		{
			intField := 1;
		}
		
		step {
			rport1 ( );
		}
	}
	
	simple.nested.rport1 = instantly simple.nested.pport1
	
	step
			ensures simple.nested.intField==1
		{
		step nested;
	}
}
