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
    using System;
    using SafetySharp.Modeling;
    using Sensors;
    using SharedComponents;

    /// <summary>
    ///   Represents the original design of the end-control.
    /// </summary>
    public class OriginalEndControl : Component, IEndControl
    {
        /// <summary>
        ///   The sensor that is used to detect vehicles in the end-control area.
        /// </summary>
        private readonly IVehicleDetector _detector;

        /// <summary>
        ///   The timer that is used to deactivate the end-control automatically.
        /// </summary>
        private readonly Timer _timer;

        /// <summary>
        ///   Indicates whether the end-control is currently active.
        /// </summary>
        private bool _active;

        /// <summary>
        ///   Initializes a new instance.
        /// </summary>
        /// <param name="detector">The sensor that should be used to detect vehicles in the end-control area.</param>
        /// <param name="timeout">The amount of time after which the end-control is deactivated.</param>
        public OriginalEndControl(IVehicleDetector detector, int timeout)
        {
            _timer = new Timer(timeout);
            _detector = detector;
        }

        /// <summary>
        ///   Gets a value indicating whether a crash is potentially imminent.
        /// </summary>
        public bool IsCrashPotentiallyImminent()
        {
            return _active && _detector.IsVehicleDetected();
        }

        /// <summary>
        ///   Signals the end-control whether it's activation has been requested.
        /// </summary>
        public extern bool ActivationRequested();

        /// <summary>
        ///   Updates the internal state of the component.
        /// </summary>
        public override void Update()
        {
            if (ActivationRequested())
            {
                _active = true;
                _timer.Start();
            }

            if (_timer.HasElapsed())
                _active = false;
        }
    }
}