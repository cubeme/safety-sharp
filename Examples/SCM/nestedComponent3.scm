component simple {
	component nested_n1 {
		component nested_n12 {
			intField1 : int = 1;
			step {
				locals{}
			}
		}
		intField1 : int = 2;
		step {
			locals{}
		}
	}
	component nested_n2 {
		component nested_n22 {
			intField1 : int = 3;
			step {
				locals{}
			}
		}
		intField1 : int = 4;
		step {
			locals{}
		}
	}
	intField1 : int = 5;
	step {
		locals{}
	}
}
