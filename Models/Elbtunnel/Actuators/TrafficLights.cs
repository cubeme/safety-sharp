namespace Elbtunnel.Actuators
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   Represents the traffic lights at the entrance of the tunnel that indicate whether the tunnel is closed.
	/// </summary>
	public class TrafficLights : Component
	{
		private bool _isRed;

		/// <summary>
		///   Switches the traffic light to red, signaling that the tunnel is closed.
		/// </summary>
		public void SwitchToRed()
		{
			_isRed = true;
		}

		/// <summary>
		///   Gets a value indicating whether the tunnel is closed.
		/// </summary>
		// TODO: Replace with property.
		public bool IsRed()
		{
			return _isRed;
		}
	}
}