component simple {
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
	pport1 ( a: int, inout b:bool) {
		locals{}
	}	
	[faultNo2]
	pport1 ( a: int, inout b:bool) {
		locals{}
	}	
	pport1 ( a: int, inout b:bool) {
		locals{}
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
