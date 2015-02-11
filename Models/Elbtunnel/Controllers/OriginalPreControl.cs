namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;
	using Sensors;

	/// <summary>
	///   Represents the simple pre-control of the Elbtunnel height control that only checks incoming overheight vehicles using a
	///   single detector.
	/// </summary>
	public class OriginalPreControl : Component, IPreControl
	{
		/// <summary>
		///   The vehicle detector that is used to detect vehicles entering the pre-control area.
		/// </summary>
		private readonly IVehicleDetector _positionDetector;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="positionDetector">
		///   The vehicle detector that should be used to detect vehicles entering the pre-control area.
		/// </param>
		public OriginalPreControl(IVehicleDetector positionDetector)
		{
			_positionDetector = positionDetector;
		}

		/// <summary>
		///   Gets the number of vehicles that entered the height control area during the current system step.
		/// </summary>
		public int GetNumberOfEnteringVehicles()
		{
			return _positionDetector.IsVehicleDetected() ? 1 : 0;
		}
	}
}