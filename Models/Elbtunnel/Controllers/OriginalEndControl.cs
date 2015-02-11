namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;
	using Sensors;
	using SharedComponents;

	/// <summary>
	///   Represents the original design of the end-control.
	/// </summary>
	public class OriginalEndControl : Component, IEndControl
	{
		/// <summary>
		///   The sensor that is used to detect vehicles in the end-control area.
		/// </summary>
		private readonly IVehicleDetector _detector;

		/// <summary>
		///   The timer that is used to deactivate the end-control automatically.
		/// </summary>
		private readonly Timer _timer;

		/// <summary>
		///   Indicates whether the end-control is currently active.
		/// </summary>
		private bool _active;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="detector">The sensor that should be used to detect vehicles in the end-control area.</param>
		/// <param name="timeout">The amount of time after which the end-control is deactivated.</param>
		public OriginalEndControl(IVehicleDetector detector, int timeout)
		{
			_timer = new Timer(timeout);
			_detector = detector;
		}

		/// <summary>
		///   Gets a value indicating whether a crash is potentially imminent.
		/// </summary>
		public bool IsCrashPotentiallyImminent()
		{
			return _active && _detector.IsVehicleDetected();
		}

		/// <summary>
		///   Signals the end-control whether it's activation has been requested.
		/// </summary>
		public extern bool ActivationRequested();

		/// <summary>
		///   Updates the internal state of the component.
		/// </summary>
		public override void Update()
		{
			if (ActivationRequested())
			{
				_active = true;
				_timer.Start();
			}

			if (_timer.HasElapsed())
				_active = false;
		}
	}
}