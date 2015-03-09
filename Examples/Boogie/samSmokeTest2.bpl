var i: int;

procedure Main() returns ()
	modifies i;
	ensures i==200;
{	
	Initialize: 
		i := 0;
		goto Node1BlockPart1;
		
	Node1BlockPart1:
		// Case distinction of Node 2
		goto Node2Option1;	
	
	Node2Option1:
		assume true;		
		i := 200;
		goto Node1BlockPart2;	
	
	Node1BlockPart2:
		//merged node 2
		return;	
}