namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   A common interface for different main-control implementations.
	/// </summary>
	public interface IMainControl : IComponent
	{
		/// <summary>
		///   Indicates whether an vehicle leaving the main-control area on the right lane has been detected.
		/// </summary>
		[Provided]
		bool IsVehicleLeavingOnRightLane();

		/// <summary>
		///   Indicates whether an vehicle leaving the main-control area on the left lane has been detected.
		/// </summary>
		[Provided]
		bool IsVehicleLeavingOnLeftLane();

		/// <summary>
		///   Gets the number of vehicles that entered the height control area during the current system step.
		/// </summary>
		[Required]
		int GetNumberOfEnteringVehicles();
	}
}