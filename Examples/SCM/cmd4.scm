component simple {
	intField : int = 0;
	
	rport1 ( a : bool , b : bool , c : bool );
	
	pport1 ( a : bool , b : bool , c : bool ) {
		locals{
		}
		choice {
			a => { intField := 1; }
			(!a) && (!b) => { intField := 2; }
			(!a) && (b) && (c)=> { intField := 3; }
		}
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		locals{
		}
		rport1 (true, true, true);
	}
}
