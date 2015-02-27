component simple {
	intField : int = 0;
	
	rport1 ( a : int , b : int );
	
	pport1 ( a : int , b : int ) {
		locals{
		}
		choice {
			a + b >= 5 && a == 0 => { intField := 1; }
			b < 5 => { intField := 2; }
			a =/= 0 && b >= 5 => { intField := 3; }
		}
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		rport1 (0, 5);
		rport1 (0, 4);
		rport1 (1, 5);
	}
}
