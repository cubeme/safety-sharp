component simple {
	intField : int = 1;
	
	rport1 ( );
	
	pport1 ( ) {
		locals {
		}
		intField := intField + 3;
	}
	
	simple.rport1 = instantly simple.pport1
	
	step {
		locals {
		}
		rport1 ( );
		
	}
}
