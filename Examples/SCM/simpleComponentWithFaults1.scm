component simple {
	fault faultNo1 {
		step {
		}
	}
	fault faultNo2 {
		step {
		}
	}
	
	[faultNo1 && ! faultNo2]
	pport1 ( in a:int, inout b:bool) {
	}	
	[faultNo2]
	pport1 ( in a:int, inout b:bool) {
	}	
	pport1 ( in a:int, inout b:bool) {
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
