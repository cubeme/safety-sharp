component simple {
	intField : int<0..100> = 0;
	
	rport1 ( in a:bool, in b:bool, in c:bool );
	
	pport1 ( in a:bool, in b:bool, in c:bool ) {
		choice {
			a => { intField := 1; }
			(!a) && (!b) => { intField := 2; }
			(!a) && (b) && (c)=> { intField := 3; }
			(!a) && (b) && (!c) => { intField := 4; }
		}
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		rport1 (in true, in true, in true);
	}
}
