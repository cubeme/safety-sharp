namespace SharedComponents
{
	using System;
	using SafetySharp.Modeling;

	public class Timer : Component
	{
		public bool Triggered = false;
		private int _i = 1;
		[Behavior]
		public void Do()
		{
			_i = _i + 1;
		}
	}
}