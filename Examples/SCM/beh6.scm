component simple {	
	boolField1 : bool = false;
	boolField2 : bool = false;
	boolField3 : bool = false;
	boolField4 : bool = false;
	intArrayField1 : Array<3,int<0..100>> = [0;0;0];
	intArrayField2 : Array<3,int<0..100>> = [0;0;0];
	boolArrayField1 : Array<3,bool> = [false;false;false];
	
	step {
		int intLocal1;
		
		foreach i in intArrayField1 {
			i := i + 1;
			intLocal := intLocal + 1;
		}
		
		boolField1 := exists i in intArrayField1 (i <= 3);
		
		boolField2 := forall i in intArrayField1 (i == 3);
		
		boolField3 := forall i,j in intArrayField1,boolArrayField1 ( i <= 30 && j == false)
		
		foreach i,j in intArrayField1,intArrayField2 {
			i := j + 1;
			intLocal := intLocal + 1;
		}
		
		foreach i*j in intArrayField1,intArrayField2 {
			choose {
					i<j => {}
					i>=j => {boolField4 := false;}
			}
		}		
	}
}


