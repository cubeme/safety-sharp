var i: int;

procedure Main() returns ()
	modifies i;
	ensures i==200;
{	
	Initialize: 
		i := 0;
		goto Node1;
		
	Node1:
		i := 200;
		return;
}