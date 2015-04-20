component simple {
	component nested {
		intField2 : int<0..100> = 0;
		faultTransientValue : int<0..100> = 0;
		
		fault faultTransient {
			step {
				choice {
					true => { faultTransientValue := 0; faultTransient := false;}
					true => { faultTransientValue := faultTransientValue+1; faultTransient := true;}
				}
			}
		}
		fault faultNever {
			step {
				faultNever := false;
			}
		}
		
		[faultTransient && ! faultNever]
		step {
			int intLocal2;
			step faultTransient;
			intField2 := intField2 + 1 + faultTransientValue;
			intLocal2 := intField2;
			step faultNever;
		}		
		step {
			int intLocal2;
			step faultTransient;
			intField2 := intField2 + 1;
			intLocal2 := intField2;
			step faultNever;			
		}
	}
	intField1 : int<0..100> = 0;
	intField3 : int<0..100> = 0;
	faultPermanentState : bool = false;
	
	fault faultPermanent {
		step {
			choice {
				faultPermanentState == true => { faultPermanentState := true; }
				faultPermanentState == false => {
					choice {
						true => {faultPermanentState := true;faultPermanent := true;}
						true => {faultPermanentState := false;faultPermanent := false;}
					}
				}
			}
		}
	}
	
	[faultPermanent]
	step {
		int intLocal1;
	}
	
	step {
		int intLocal1;
		intField1 := intField1 + 1;
		step nested;
		intLocal1 := intField1;
		step faultPermanent;
		intField3 := intField1 + 1;
	}
}
