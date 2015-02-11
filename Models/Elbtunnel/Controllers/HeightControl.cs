namespace Elbtunnel.Controllers
{
	using System;
	using Actuators;
	using SafetySharp.Modeling;

	/// <summary>
	///   Represents the height control of the Elbtunnel.
	/// </summary>
	public class HeightControl : Component
	{
		/// <summary>
		///   The end-control step of the height control.
		/// </summary>
		private readonly IEndControl _endControl;

		/// <summary>
		///   The main-control step of the height control.
		/// </summary>
		private readonly IMainControl _mainControl;

		/// <summary>
		///   The pre-control step of the height control.
		/// </summary>
		private readonly IPreControl _preControl;

		/// <summary>
		///   The traffic lights that are used to signal that the tunnel is closed.
		/// </summary>
		private readonly TrafficLights _trafficLights;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="preControl">The pre-control step of the height control.</param>
		/// <param name="mainControl">The main-control step of the height control.</param>
		/// <param name="endControl">The end-control step of the height control.</param>
		/// <param name="trafficLights">The traffic lights that are used to signal that the tunnel is closed.</param>
		public HeightControl(IPreControl preControl, IMainControl mainControl, IEndControl endControl, TrafficLights trafficLights)
		{
			_preControl = preControl;
			_mainControl = mainControl;
			_endControl = endControl;
			_trafficLights = trafficLights;

			Bind(_mainControl.RequiredPorts.GetNumberOfEnteringVehicles = _preControl.ProvidedPorts.GetNumberOfEnteringVehicles);
			Bind(_endControl.RequiredPorts.ActivationRequested = _mainControl.ProvidedPorts.IsVehicleLeavingOnRightLane);
		}

		/// <summary>
		///   Updates the internal state of the component.
		/// </summary>
		public override void Update()
		{
			if (_mainControl.IsVehicleLeavingOnLeftLane() || _endControl.IsCrashPotentiallyImminent())
				_trafficLights.SwitchToRed();
		}
	}
}