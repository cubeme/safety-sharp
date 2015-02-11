namespace Elbtunnel.Environment
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   A common interface for vehciles using the tunnel.
	/// </summary>
	public interface IVehicle : IComponent
	{
		/// <summary>
		///   Gets the current position of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		[Provided]
		int GetPosition();

		/// <summary>
		///   Gets the current speed of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		[Provided]
		int GetSpeed();

		/// <summary>
		///   Gets the current lane of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		[Provided]
		Lane GetLane();

		/// <summary>
		///   Gets the kind the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		[Provided]
		VehicleKind GetKind();

		/// <summary>
		///   Informs the vehicle whether the tunnel is closed.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		[Required]
		bool IsTunnelClosed();
	}
}