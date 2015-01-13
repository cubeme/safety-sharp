component simple {
	fault faultNo1 {
		step {
			locals{}
			choice {
				true => { faultNo1 := false;}
				true => { faultNo1 := true;}
			}
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
		step faultNo1;
	}
	[faultNo2]
	step {
		locals{}
		step faultNo1;
	}
	step {
		locals{}
		step faultNo1;
	}
}
