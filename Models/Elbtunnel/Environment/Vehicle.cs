namespace Elbtunnel.Environment
{
	using System;
	using SafetySharp.Modeling;

	/// <summary>
	///   Represents an overheight vehicle that is not allowed to enter the tunnel on the left lane.
	/// </summary>
	public class Vehicle : Component, IVehicle
	{
		/// <summary>
		///   The kind of the vehicle.
		/// </summary>
		private readonly VehicleKind _kind;

		/// <summary>
		///   The current lane of the vehicle.
		/// </summary>
		private Lane _lane;

		/// <summary>
		///   The current position of the vehicle.
		/// </summary>
		private int _position;

		/// <summary>
		///   The current speed of the vehicle.
		/// </summary>
		private int _speed;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="kind">The kind of the vehicle.</param>
		public Vehicle(VehicleKind kind)
		{
			_kind = kind;
			SetInitialValues(_lane, Lane.Left, Lane.Right);
		}

		/// <summary>
		///   Gets the current position of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		public int GetPosition()
		{
			return _position;
		}

		/// <summary>
		///   Gets the current speed of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		public int GetSpeed()
		{
			return _speed;
		}

		/// <summary>
		///   Gets the current lane of the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		public Lane GetLane()
		{
			return _lane;
		}

		/// <summary>
		///   Gets the kind the vehicle.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		public VehicleKind GetKind()
		{
			return _kind;
		}

		/// <summary>
		///   Informs the vehicle whether the tunnel is closed.
		/// </summary>
		// TODO: Use a property once supported by the S# compiler.
		public extern bool IsTunnelClosed();

		/// <summary>
		///   Updates the vehicles internal state.
		/// </summary>
		public override void Update()
		{
			if (IsTunnelClosed())
			{
				_speed = 0;
				return;
			}

			// TODO: Support nondeterministic choices
			_speed = 7;
			_lane = Lane.Left;

			// TODO: Support different system step times
			_position += _speed;
		}
	}
}