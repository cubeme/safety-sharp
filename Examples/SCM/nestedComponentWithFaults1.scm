component simple {
	component nested {
		intField1 : int<0..100> = 2;
		intField2 : int<0..100> = 1;
		intField5 : int<0..100> = 3;
		fault faultNo1 {
			step {
			}
		}
		fault faultNo2 {
			step {
			}
		}
		[faultNo1 && ! faultNo2]
		step {
		}
		[faultNo2]
		step {
		}
		step {
		}
	}
	intField1 : int<0..100> = 5;
	step {
	}
}
