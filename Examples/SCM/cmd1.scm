component simple {
	intField : int = 1 2;
	
	step {
		locals{
		}
		choice {
			intField == 1 => { intField := 10 }
			intField == 2 => { intField := 20 }
			6 > 4 => { intField := 30 }
			4 < 5 => { intField := 40 }
			4 < 5 => { intField := 50 }
			true => { intField := 60 }
			false => { intField := 70 } ;
		}
		
		intField := intField + 1;
	}
}
