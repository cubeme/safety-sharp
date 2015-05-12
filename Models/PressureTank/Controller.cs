// The MIT License (MIT)
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

namespace PressureTank
{
    using SafetySharp.Modeling;
    using SharedComponents;

    /// <summary>
    ///   The software controller that enables and disables the pump.
    /// </summary>
    public class Controller : Component
    {
        /// <summary>
        ///   The pump that is used to fill the tank.
        /// </summary>
        private readonly Pump _pump;

        /// <summary>
        ///   The sensor that is used to sense the pressure level within the tank.
        /// </summary>
        private readonly Sensor _sensor;

        /// <summary>
        ///   The timer that is used to determine whether the pump should be disabled to prevent tank ruptures.
        /// </summary>
        private readonly Timer _timer;

        /// <summary>
        ///   Initializes a new instance.
        /// </summary>
        /// <param name="sensor">The sensor that is used to sense the pressure level within the tank.</param>
        /// <param name="pump">The pump that is used to fill the tank.</param>
        /// <param name="timer">The timer that is used to determine whether the pump should be disabled.</param>
        public Controller(Sensor sensor, Pump pump, Timer timer)
        {
            _pump = pump;
            _sensor = sensor;
            _timer = timer;

            _timer.Start();
        }

        /// <summary>
        ///   Updates the controller's internal state.
        /// </summary>
        public override void Update()
        {
            // We're only interested in a single cycle at the moment, so the pump is enabled
            // at the beginning and disabled by the controller once the sensor triggers or
            // the timer times out. We do not care what happens after that, i.e., refilling
            // the tank once it has been depleted, etc.

            if (_pump.IsEnabled())
            {
                var shouldStop = _sensor.IsTriggered() || _timer.HasElapsed();

                if (shouldStop)
                    _pump.Disable();

                if (_sensor.IsTriggered())
                    _timer.Stop();
            }
        }
    }
}