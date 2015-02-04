namespace SharedComponents
{
	using System;
	using SafetySharp.Modeling;

	public class Timer : Component
	{
	    public Timer(int timeout)
	    {
	        _timeout = timeout;
	    }

		//public bool Triggered = false;
	    private readonly int _timeout;

		private int _i = 1;

		public extern void Test();

	    [Provided]
	    public bool Triggered()
	    {
	        return (_i >= _timeout);
	    }

	    [Provided]
	    public void Reset()
	    {
		    Test();
	        _i = 0;
	    }

		public override void Update()
		{
			_i = _i + 1;
		}
	}
}