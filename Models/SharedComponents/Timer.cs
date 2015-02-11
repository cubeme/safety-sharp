namespace SharedComponents
{
	using System;
	using SafetySharp.Modeling;

	public class Timer : Component
	{
		private readonly int _timeout;

		// TODO: OverflowBehavior.Clamp
		private int _remainingTime;

		public Timer(int timeout)
		{
			_timeout = timeout;
		}

		public bool HasElapsed()
		{
			return _remainingTime == 0;
		}

		public void Start()
		{
			_remainingTime = _timeout;
		}

		public void Stop()
		{
			_remainingTime = 0;
		}

		public override void Update()
		{
			// TODO: Support different system step times
			--_remainingTime;
		}
	}
}