component simple {	
	component nested {
		intField2 : int = 0;
		step {			
			locals{
				intLocal2 : int;
			}
			intField2 := intField2 + 1;
			intLocal2 := intField2;
			choice {
				false => { }
			}
		}
	}
	intField1 : int = 0;
	intField3 : int = 0;	
	step {		
		locals{
			intLocal1 : int;
		}
		intField1 := intField1 + 1;
		step nested;
		intLocal1 := intField1;
		intField3 := intField1 + 1;
	}
}
