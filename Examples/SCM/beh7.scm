component simple {	
	bool boolField1 : bool = false;
	int intField1 : int<0..100> = 0;
		
	boolArrayInArrayField1 : Array<4,Array<2,bool>> = [[true;true];[true;false];[false;false];[false;false]];
	
	step {		
		foreach i in boolArrayInArrayField1 {
			foreach j in i {
				choose {
					j == true => {intLocal1 := intField1 + 1;}
					j == false => {}
				}
			}
		}		
		boolField1 := exists i in boolArrayInArrayField1 ( forall j in i (j==true));
	}
}


