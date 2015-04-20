component simple {
	component nested_n1 {
		component nested_n12 {
			intField1 : int<0..100> = 1;
			step {
			}
		}
		intField1 : int<0..100> = 2;
		step {
		}
	}
	component nested_n2 {
		component nested_n22 {
			intField1 : int<0..100> = 3;
			step {
			}
		}
		intField1 : int<0..100> = 4;
		step {
		}
	}
	intField1 : int<0..100> = 5;
	step {
	}
}
