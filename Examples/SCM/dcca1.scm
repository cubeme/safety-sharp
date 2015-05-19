component simple {
	isHazard : bool = false;
	fault faultNo1 {
		step {
			choice {
				true => {faultNo1:=true;}
				true => {faultNo1:=false;}
			}
		}
	}
	fault faultNo2 {
		step {
			choice {
				true => {faultNo2:=true;}
				true => {faultNo2:=false;}
			}
		}
	}
	fault faultNo3 {
		step {
			choice {
				true => {faultNo3:=true;}
				true => {faultNo3:=false;}
			}
		}
	}
	fault faultNo4 {
		step {
			choice {
				true => {faultNo4:=true;}
				true => {faultNo4:=false;}
			}
		}
	}
	[faultNo1 && faultNo2]
	step {
		step faultNo1;
		step faultNo2;
		step faultNo3;
		step faultNo4;
		isHazard := true;
	}
	[faultNo1 && faultNo4]
	step {
		step faultNo1;
		step faultNo2;
		step faultNo3;
		step faultNo4;
		isHazard := true;
	}
	[faultNo2 && faultNo3 && faultNo4]
	step {
		step faultNo1;
		step faultNo2;
		step faultNo3;
		step faultNo4;
		isHazard := true;
	}
	
	step {
		step faultNo1;
		step faultNo2;
		step faultNo3;
		step faultNo4;
		isHazard := false;
	}
}