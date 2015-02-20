component simple {	
	component nested {
		intField2 : int = 0;
		step {
			locals {
				int intLocal2;
			}
			intField2 := intField2 + 1;
			intLocal2 := intField2;
		}
		formula-invar nested.intField2 >= 0;
	}
	intField1 : int = 0;
	intField3 : int = 0;
	step {
		locals {
			int intLocal1;			
		}
		intField1 := intField1 + 1;
		step nested;
		intLocal1 := intField1;
		intField3 := intField1 + 1;
	}
	formula-invar simple.intField3 >= simple.intField1;
}
