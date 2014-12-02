component simple {
	component nested {
		nestedIntField : int = 5;
		step {
			locals{}
		}
	}
	pport1 ( ) {
		locals{}
		nestedIntField :=5;
	}
	
	
	step {
		locals{}
	}
}
