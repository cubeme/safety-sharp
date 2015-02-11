namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;
	using Sensors;

	/// <summary>
	///   Represents a more sophisticated pre-control of the Elbtunnel height control that uses additional sensors to detect
	///   vehicles entering the height control area.
	/// </summary>
	public class RevisedPreControl : Component, IPreControl
	{
		/// <summary>
		///   The sensor that detects vehicles on the left lane.
		/// </summary>
		private readonly IVehicleDetector _leftDetector;

		/// <summary>
		///   The sensor that detects vehicles on any lane.
		/// </summary>
		private readonly IVehicleDetector _positionDetector;

		/// <summary>
		///   The sensor that detects vehicles on the right lane.
		/// </summary>
		private readonly IVehicleDetector _rightDetector;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="positionDetector">The sensor that detects vehicles on any lane.</param>
		/// <param name="leftDetector">The sensor that detects vehicles on the left lane.</param>
		/// <param name="rightDetector">The sensor that detects vehicles on the right lane.</param>
		public RevisedPreControl(IVehicleDetector positionDetector, IVehicleDetector leftDetector, IVehicleDetector rightDetector)
		{
			_positionDetector = positionDetector;
			_leftDetector = leftDetector;
			_rightDetector = rightDetector;
		}

		/// <summary>
		///   Gets the number of vehicles that entered the height control area during the current system step.
		/// </summary>
		public int GetNumberOfEnteringVehicles()
		{
			if (_positionDetector.IsVehicleDetected() && _leftDetector.IsVehicleDetected() && _rightDetector.IsVehicleDetected())
				return 2;

			if (_positionDetector.IsVehicleDetected() && (_leftDetector.IsVehicleDetected() || _rightDetector.IsVehicleDetected()))
				return 1;

			return 0;
		}
	}
}