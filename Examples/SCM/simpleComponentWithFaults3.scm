component simple {
	
	intField1 : int = 0;
	
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
			choice {
				true => { faultNo2 := false;}
				true => { faultNo2 := true;}
			}
		}
	}
		
	[faultNo1 && ! faultNo2]
	step {
		locals{}
		step faultNo1;
		step faultNo2;
		intField1 := 2;
	}
	[faultNo2]
	step {
		locals{}
		step faultNo1;
		step faultNo2;
		intField1 := 3;
	}
	step {
		locals{}
		step faultNo1;
		step faultNo2;
		intField1 := 1;
	}
}
