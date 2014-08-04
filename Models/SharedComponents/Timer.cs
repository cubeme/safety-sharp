namespace SharedComponents
{
	using System;
	using SafetySharp.Modeling;

	public class Timer : Component
	{
		public bool Triggered = false;
		private int _i = 1;
		public override void Update()
		{
			_i = _i + 1;
		}
	}
}