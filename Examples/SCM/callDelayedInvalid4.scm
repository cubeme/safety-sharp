component simple {
	intField1 : int = 0;
	
	rport1 ( );

	pport1 ( )  {
		locals{
		}
		intField1 := intField1 + 1;
	}	
	
	
	rport1 = delayed pport1
	
	
	step {
		locals{
		}
		rport1();
	}
}
