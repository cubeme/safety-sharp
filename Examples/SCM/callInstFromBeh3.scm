component simple {
	intField : int = 1;
	
	rport1 ( );
	
	pport1 ( ) {
		locals {
		}
		intField := intField + 3;
	}
	
	rport1 = instantly pport1
	
	step {
		locals {
		}
		rport1 ( );
		
	}
}
