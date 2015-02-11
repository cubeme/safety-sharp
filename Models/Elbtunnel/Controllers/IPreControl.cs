namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   A common interface for different pre-control implementations.
	/// </summary>
	public interface IPreControl : IComponent
	{
		/// <summary>
		///   Gets the number of vehicles that entered the height control area during the current system step.
		/// </summary>
		[Provided]
		int GetNumberOfEnteringVehicles();
	}
}