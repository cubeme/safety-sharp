﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace Elbtunnel.Sensors
{
	using SafetySharp.Modeling;

	/// <summary>
	///   Represents a light barrier that detects overheight vehicles at a specific position on any of the lanes.
	/// </summary>
	public class LightBarrier : Component, IVehicleDetector
	{
		/// <summary>
		///   The position of the light barrier. When an overheight vehicle passes this position, it is detected by the light barrier.
		/// </summary>
		private readonly int _position;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="position">
		///   The position of the light barrier. When an overheight vehicle passes this position, it is detected by
		///   the light barrier.
		/// </param>
		public LightBarrier(int position)
		{
			_position = position;
		}

		/// <summary>
		///   Indicates whether the light barrier detected a vehicle.
		/// </summary>
		public bool IsVehicleDetected()
		{
			// TODO: We hardcode 3 overheight vehicles for the time being. This can be removed once S# supports arrays.
			return CheckVehicle(0) || CheckVehicle(1) || CheckVehicle(2);
		}

		/// <summary>
		///   Gets the position of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		public extern int GetVehiclePosition(int vehicleIndex);

		/// <summary>
		///   Gets the speed of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port once S# supports more environment modeling techniques that make the range checks in <see cref="CheckVehicle" /> unnecessary.
		public extern int GetVehicleSpeed(int vehicleIndex);

		/// <summary>
		///   Gets the speed of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		public extern VehicleKind GetVehicleKind(int vehicleIndex);

		/// <summary>
		///   Gets the lane of the vehicle with the given <paramref name="vehicleIndex" />.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		// TODO: Replace this port by an array-based version once S# supports arrays.
		public extern Lane GetVehicleLane(int vehicleIndex);

		/// <summary>
		///   Gets a value indicating whether the light barrier detects the vehicle with the given position and speed.
		/// </summary>
		/// <param name="vehicleIndex">The index of the vehicle that should be checked.</param>
		private bool CheckVehicle(int vehicleIndex)
		{
			return GetVehicleKind(vehicleIndex) == VehicleKind.OverheightTruck &&
				   GetVehiclePosition(vehicleIndex) >= _position &&
				   GetVehiclePosition(vehicleIndex) + GetVehicleSpeed(vehicleIndex) < _position;
		}
	}
}