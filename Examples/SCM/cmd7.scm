component simple {
	intField : int<0..100> = 0;
	
	rport1 ( in a:int , in b:int );
	
	pport1 ( in a:int , in b:int ) {
		choice {
			a + b >= 5 && a == 0 => { intField := 1; }
			b < 5 => { intField := 2; }
			a =/= 0 && b >= 5 => { intField := 3; }
		}
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		rport1 (in 0, in 5);
		rport1 (in 0, in 4);
		rport1 (in 1, in 5);
	}
}
