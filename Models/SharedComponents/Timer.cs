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

namespace SharedComponents
{
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;

	/// <summary>
	///   Represents a timer that signals a timeout.
	/// </summary>
	public class Timer : Component
	{
		/// <summary>
		///   The timeout signaled by the timer.
		/// </summary>
		private readonly int _timeout;

		/// <summary>
		///   The remaining time before the timeout is signaled. A value of -1 indicates that the timer is inactive.
		/// </summary>
		// TODO: OverflowBehavior.Clamp
		private int _remainingTime = -1;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="timeout">The timeout interval of the timer.</param>
		public Timer(int timeout)
		{
			_timeout = timeout;
		}

		/// <summary>
		///   Gets a value indicating whether the timeout has elapsed. This method returns true only for the single system step where
		///   the timeout occurs.
		/// </summary>
		public bool HasElapsed() => _remainingTime == 0;

		/// <summary>
		///   Starts or restarts the timer.
		/// </summary>
		public void Start() => _remainingTime = _timeout;

		/// <summary>
		///   Stops the timer.
		/// </summary>
		public void Stop() => _remainingTime = -1;

		/// <summary>
		///   Gets a value indicating whether the timer is currently active, eventually signalling the timeout.
		/// </summary>
		public bool IsActive() => _remainingTime > 0;

		/// <summary>
		///   Gets the remaining time before the timeout occurs.
		/// </summary>
		public int GetRemainingTime() => _remainingTime;

		/// <summary>
		///   Updates the timer's internal state.
		/// </summary>
		public override void Update()
		{
			// TODO: Support different system step times
			--_remainingTime;
		}

		/// <summary>
		///   Represents a failure mode that prevents the timer from reporting a timeout.
		/// </summary>
		[Transient]
		public class SuppressTimeout : Fault
		{
			public bool HasElapsed() => false;
		}
	}
}