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

namespace Elbtunnel
{
	using System;
	using System.Diagnostics;
	using Actuators;
	using Controllers;
	using Environment;
	using NUnit.Framework;
	using SafetySharp.Analysis;
	using SafetySharp.Modeling;
	using Sensors;

	[TestFixture]
	public class Tests
	{
		[SetUp]
		public void Initialize()
		{
			var lightBarrier1 = new LightBarrier(position: 200);
			var lightBarrier2 = new LightBarrier(position: 400);

			var detectorLeft = new OverheadDetector(Lane.Left, position: 400);
			var detectorRight = new OverheadDetector(Lane.Right, position: 400);
			var detectorFinal = new OverheadDetector(Lane.Left, position: 600);

			var trafficLights = new TrafficLights();

			var preControl = new OriginalPreControl(lightBarrier1);
			var mainControl = new OriginalMainControl(lightBarrier2, detectorLeft, detectorRight, timeout: 30);
			var endControl = new OriginalEndControl(detectorFinal, timeout: 10);

			var vehicle1 = new Vehicle(VehicleKind.OverheightTruck);
			var vehicle2 = new Vehicle(VehicleKind.Truck);
			var vehicle3 = new Vehicle(VehicleKind.OverheightTruck);

			var heightControl = new HeightControl(preControl, mainControl, endControl, trafficLights);
			var vehicles = new VehicleCollection(vehicle1, vehicle2, vehicle3);

			_model = new Model(heightControl, vehicles);

			Bind(vehicles, lightBarrier1);
			Bind(vehicles, lightBarrier2);
			Bind(vehicles, detectorLeft);
			Bind(vehicles, detectorRight);
			Bind(vehicles, detectorFinal);

			_model.Bind(vehicles.RequiredPorts.IsTunnelClosed = trafficLights.ProvidedPorts.IsRed).Delayed();
		}

		private Model _model;

		private void Bind(VehicleCollection vehicles, IVehicleDetector detector)
		{
			_model.Bind(detector.RequiredPorts.GetVehicleKind = vehicles.ProvidedPorts.GetVehicleKind);
			_model.Bind(detector.RequiredPorts.GetVehiclePosition = vehicles.ProvidedPorts.GetVehiclePosition);
			_model.Bind(detector.RequiredPorts.GetVehicleSpeed = vehicles.ProvidedPorts.GetVehicleSpeed);
			_model.Bind(detector.RequiredPorts.GetVehicleLane = vehicles.ProvidedPorts.GetVehicleLane);
		}

		private static void Main()
		{
			var tests = new Tests();
			tests.Initialize();
			tests.FirstTest();
		}

		[Test]
		public void FirstTest()
		{
			var watch = new Stopwatch();
			watch.Start();
			var spin = new SpinModelChecker(_model);
			Console.WriteLine("Elapsed: {0}ms", watch.Elapsed.TotalMilliseconds);
		}
	}
}