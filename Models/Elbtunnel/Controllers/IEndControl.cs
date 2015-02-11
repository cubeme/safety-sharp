namespace Elbtunnel.Controllers
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   A common interface for different end-control implementations.
	/// </summary>
	public interface IEndControl : IComponent
	{
		/// <summary>
		///   Gets a value indicating whether a crash is potentially imminent.
		/// </summary>
		[Provided]
		bool IsCrashPotentiallyImminent();

		/// <summary>
		///   Signals the end-control whether it's activation has been requested.
		/// </summary>
		[Required]
		bool ActivationRequested();
	}
}