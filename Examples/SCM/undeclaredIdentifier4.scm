component simple {
	component nested {
		nestedIntField : int<0..100> = 5;
		step {
		}
	}
	pport1 ( ) {
		nestedIntField :=5;
	}
		
	step {
	}
}
