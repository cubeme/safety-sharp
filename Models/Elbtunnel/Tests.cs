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
		private Model _model;

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

			_model = new Model();
			_model.SetRootComponents(heightControl, vehicles);

			Bind(vehicles, lightBarrier1);
			Bind(vehicles, lightBarrier2);
			Bind(vehicles, detectorLeft);
			Bind(vehicles, detectorRight);
			Bind(vehicles, detectorFinal);

			_model.Bind(vehicles.RequiredPorts.IsTunnelClosed = trafficLights.ProvidedPorts.IsRed).Delayed();
		}

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