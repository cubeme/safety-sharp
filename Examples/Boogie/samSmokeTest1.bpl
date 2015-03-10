var i: int;

procedure Main() returns ()
	modifies i;
{
	var counter: int;
	
	Initialize: 
		i := 0;
		counter := 0;
		goto LoopHead,End;
	
	LoopHead:
		assume counter < 5;
		call Loop ();
		assert i == 200;
		counter := counter + 1;
		goto LoopHead,End;
	
	End:
		assume counter == 5;
		return;
}

procedure Loop() returns ()
	modifies i;
	ensures i == 200;
{
	Node1Block:
		i := 200;
		return;
}