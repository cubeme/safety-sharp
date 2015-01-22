// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

using System.Runtime.InteropServices;
using SharedComponents;

namespace PressureTank
{
	using System;
	using System.Diagnostics;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	internal class PressureSensor : Component
	{
		public const int MaxPressure = 40;

		[Required]
		public extern int SensePressure();

		[Provided]
		public bool Triggered()
		{
			return SensePressure() >= MaxPressure;
		}

		//[Transient]
		internal class ReportOk
		{
			[Provided]
			public bool Triggered()
			{
				return false;
			}
		}
	}

	internal class Controller : Component
	{
		private readonly PressureSensor _sensor;
		private readonly Pump _pump;
		private readonly Timer _timer;
		private enum PressureTankState
		{
			Filling, Draining, EmergencyStop
		}
		private PressureTankState _currentState = PressureTankState.Filling;

		public Controller(PressureSensor sensor,Pump pump)
		{
			_sensor = sensor;
			_pump = pump;
			_timer = new Timer(60);
		}
	
		public override void Update()
		{
			_timer.Update();
			switch (_currentState)
			{
				case PressureTankState.Filling:
					if (_sensor.Triggered())
					{
						_currentState = PressureTankState.Draining;
					}
					else if (_timer.Triggered())
					{
						_currentState = PressureTankState.EmergencyStop;
					}
					else
					{
						//_pump.Fill();
					}
					break;
				case PressureTankState.Draining:
					if (!_sensor.Triggered())
					{
						_currentState = PressureTankState.Filling;
						_timer.Reset();
					}
					break;
				case PressureTankState.EmergencyStop:
					break;
				default:
					throw new ArgumentOutOfRangeException();
			}
			
		} 
	}

	internal class PressureTank : Component
	{
		private int _pressure = 0;
		private bool _wasFilledInThisCycle = true;

		[Provided]
		public void Fill()
		{
			_wasFilledInThisCycle = true;
			_pressure += 1;
		}

		[Provided]
		public int CurrentPressure()
		{
			return _pressure;
		}

		public override void Update()
		{
			if (!_wasFilledInThisCycle)
				_pressure += 0;
			_wasFilledInThisCycle = false;
		}
		
	}

	internal class Pump : Component
	{
		[Required]
		public extern void Fill();
	}

	class Program
	{
		static void Main(string[] args)
		{
			var _pt = new PressureTank();
			var _pump = new Pump();
			var _sensor = new PressureSensor();
			var _ctl = new Controller(_sensor,_pump);

			//Bind(_pump.Fill(),_pt.Fill());
			//Bind(_sensor.SensePressure(),_pt.CurrentPressure());

		}

		[Test]
		void TimerShouldPreventRuptureIfSensorFails()
		{
			//var model = ;// configure the model
			//var simulation = new Simulation(model);
			//simulation.EnableFault<PressureSensor.ReportOk>(after: 10 /* seconds */);
			//
			//simulation.Advance(70 /* seconds */);
			//Assert.That(!model.PressureTank.IsRuptured);
		}
	}
}
