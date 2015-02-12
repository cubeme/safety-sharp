component C {
	component D {
		b : bool = false;
		
		Y ()
		
		X (p1 : int, p2 : int, inout r1 : bool, inout r2 : bool) {
			locals{}
			Y();
			r1 := false ;
			r2 := b;
		}
				
		step {
			locals{}
		}
	}

	x : int = 1, 2, 3;
	b : bool= true, false;
		
	M (input1 : int, input2 : int, inout inout1: bool, inout inout2 : bool);
		
	X (p1 : int, p2 : int , inout r1 : bool, inout r2 : bool) {
		locals{}
		r1 := p1 > 1 ;
		r2 := p2 > x && b;
	}	
	
	Y () {
		locals{}
	}
		
	C.M = delayed C.D.X
	C.D.Y = instantly C.Y
	
	step {
		locals{
			bool l1;
			bool l2;
		}
		M(x, x - 1, inout l1, inout l2) ;
		choice {
			l1 => { x := x - 1; }
			l2 => { b := true; } ;
		}
		step D;
	}
}
