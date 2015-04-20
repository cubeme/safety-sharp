component simple {
	component nested {
		step {
			int localVal1;
			localVal1 := 5+3;
		}
	}
	intField1 : int<0..100> = 5;
	step {
	}
}
