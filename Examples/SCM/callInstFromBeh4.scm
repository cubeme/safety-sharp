component simple {
	intField : int = 1;
	
	rport1 ( r_input1 : int, r_input2 : int );
	
	pport1 ( p_input1 : int, p_input2  : int ) {
		locals{
		}
		intField := intField + p_input1 + p_input2;		
	}
	
	rport1 = instantly pport1 
	
	step {		
		locals{
			int intLocal;
		}
		intLocal := 4 ;
		rport1 ( 5 + 7 , intLocal);
	}
}
