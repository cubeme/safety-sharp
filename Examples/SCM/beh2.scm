component simple {	
	component nested {
		intField2 : int = 0;
		step {
			locals { }
			intField2 := intField2 + 1;
		}
	}
	intField1 : int = 0;
	intField3 : int = 0;	
	step {
		locals { }
		intField1 := intField1 + 1;
		step nested;
		intField3 := intField1 + 1;
	}
}
