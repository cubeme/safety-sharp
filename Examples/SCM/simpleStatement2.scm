component simple {
	intField1 : int = 0, 1;
	
	step {
		locals{}
		intField1 := intField1 + 3;
	}
}
