component simple {
	component nested {
		intField1 : int = 2;
		intField2 : int = 1;
		intField5 : int = 3;
		fault faultNo1 {
			step {
				locals{}
			}
		}
		fault faultNo2 {
			step {
				locals{}
			}
		}
		[faultNo1 && ! faultNo2]
		step {
			locals{}
		}
		[faultNo2]
		step {
			locals{}
		}
		step {
			locals{}
		}
	}
	intField1 : int = 5;
	step {
		locals{}
	}
}
