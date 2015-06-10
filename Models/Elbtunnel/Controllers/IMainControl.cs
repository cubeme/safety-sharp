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

namespace Elbtunnel.Controllers
{
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