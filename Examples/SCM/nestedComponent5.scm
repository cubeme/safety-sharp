component simple {
	component nested {
		step {
			locals{
				int localVal1;
			}
			localVal1 := 5+3;
		}
	}
	intField1 : int = 5;
	step {
		locals{}
	}
}
