namespace Elbtunnel.Sensors
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   A common interface for sensors that detect vehicles.
	/// </summary>
	public interface IVehicleDetector : IComponent
	{
		/// <summary>
		///   Indicates whether the sensor detected a vehicle.
		/// </summary>
		[Provided]
		bool IsVehicleDetected();

		/// <summary>
		///   Gets the position of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		[Required]
		int GetVehiclePosition(int vehicleIndex);

		/// <summary>
		///   Gets the speed of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port once S# supports more environment modeling techniques that make the range checks in <see cref="CheckVehicle" /> unnecessary.
		[Required]
		int GetVehicleSpeed(int vehicleIndex);

		/// <summary>
		///   Gets the speed of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		[Required]
		VehicleKind GetVehicleKind(int vehicleIndex);

		/// <summary>
		///   Gets the lane of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		[Required]
		Lane GetVehicleLane(int vehicleIndex);
	}
}