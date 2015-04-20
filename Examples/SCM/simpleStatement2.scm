component simple {
	intField1 : int<0..100> = 0, 1;
	
	step {
		intField1 := intField1 + 3;
	}
}
