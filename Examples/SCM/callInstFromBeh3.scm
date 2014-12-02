component simple {
	intField : int = 1;
	
	rport1 r( );
	
	pport1 p( ) {
		locals {
		}
		intField := intField + 3;
	}
	
	rport1 = instantly pport1;
	
	step {
		locals {
		}
		rport1 ( )
		
	}
}
