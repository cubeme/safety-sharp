component C {
	component D {
		b : bool = false;
		
		Y ()
		
		X (in p1:int, in p2:int, inout r1:bool, inout r2:bool) {
			Y();
			r1 := false ;
			r2 := b;
		}
				
		step {
		}
	}

	x : int<0..100> = 1, 2, 3;
	b : bool = true, false;
		
	M (in input1:int, in input2:int, inout inout1:bool, inout inout2:bool);
		
	X (in p1:int, in p2:int , inout r1:bool, inout r2:bool) {
		r1 := p1 > 1 ;
		r2 := p2 > x && b;
	}	
	
	Y () {
	}
		
	C.M = instantly C.D.X
	C.D.Y = instantly C.Y
	
	step {
		bool l1;
		bool l2;
		M(x, x - 1, inout l1, inout l2) ;
		choice {
			l1 => { x := x - 1; }
			l2 => { b := true; } ;
		}
		step D;
	}
}
