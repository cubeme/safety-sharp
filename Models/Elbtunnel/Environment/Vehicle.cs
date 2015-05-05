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