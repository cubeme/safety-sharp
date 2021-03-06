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

namespace PressureTank
{
	using System;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Analysis;
	using SafetySharp.Simulation;
	using SharedComponents;
	using static SafetySharp.Analysis.Ltl;

	internal class Program
	{
		private static void Main()
		{
			var tests = new Tests();
			tests.TankDoesNotRuptureWhenNoFaultsOccur();
		}
	}

	[TestFixture]
	public class ModelCheckingTests
	{
		private readonly PressureTankModel _model;
		private readonly Spin _spin;

		public ModelCheckingTests()
		{
			_model = new PressureTankModel();
			_spin = new Spin(_model);
		}

		[Test]
		public void PressureIsIncreased()
		{
			_spin.Check(F(_model.Tank.PressureLevel() > 0));
		}

		[Test]
		public void TimerNeverOpensWhenSensorIsAlwaysWorking()
		{
			_spin.Check(G(!IsOccurring<Sensor.SuppressIsFull>(_model.Sensor)).Implies(!F(_model.Timer.HasElapsed())));
		}

		[Test]
		public void TimerOpensWhenSensorIsNotWorking()
		{
			_spin.Check(F(G(IsOccurring<Sensor.SuppressIsFull>(_model.Sensor))).Implies(F(_model.Timer.HasElapsed())));
		}

		[Test]
		public void TankDoesNotRuptureWhenNoFaultsOccur()
		{
			_spin.Check(
				G(!IsOccurring<Sensor.SuppressIsFull>(_model.Sensor) & !IsOccurring<Timer.SuppressTimeout>(_model.Timer))
					.Implies(!F(_model.Tank.IsRuptured())));
		}

		[Test]
		public void TankDoesNotRuptureWhenSensorDoesNotReportTankFull()
		{
			_spin.Check(
				G(IsOccurring<Sensor.SuppressIsFull>(_model.Sensor) & !IsOccurring<Timer.SuppressTimeout>(_model.Timer))
					.Implies(!F(_model.Tank.IsRuptured())));
		}

		[Test]
		public void TankRupturesWhenSensorDoesNotReportTankFullAndTimerDoesNotTimeout()
		{
			_spin.Check(
				F(G(IsOccurring<Sensor.SuppressIsFull>(_model.Sensor) & IsOccurring<Timer.SuppressTimeout>(_model.Timer)))
					.Implies(!F(_model.Tank.IsRuptured())));
		}

		[Test]
		public void SafetyAnalysis()
		{
			_spin.ComputeMinimalCriticalSets(_model.Tank.IsRuptured());
		}
	}

	[TestFixture]
	public class Tests
	{
		[Test]
		public void TankDoesNotRuptureWhenNoFaultsOccur()
		{
			// Arrange
			var model = new PressureTankModel();
			var simulator = new Simulator(model);

			// Act
			simulator.Simulate(TimeSpan.FromHours(1));

			// Assert
			model.Tank.IsRuptured().Should().BeFalse();
		}

		[Test]
		public void TankDoesNotRuptureWhenSensorDoesNotReportTankFull()
		{
			// Arrange
			var model = new PressureTankModel();
			var simulator = new Simulator(model);
			model.Sensor.EnableFault<Sensor.SuppressIsFull>();

			// Act
			simulator.Simulate(TimeSpan.FromHours(1));

			// Assert
			model.Tank.IsRuptured().Should().BeFalse();
		}

		[Test]
		public void TankRupturesWhenSensorDoesNotReportTankFullAndTimerDoesNotTimeout()
		{
			// Arrange
			var model = new PressureTankModel();
			var simulator = new Simulator(model);
			model.Sensor.EnableFault<Sensor.SuppressIsFull>();
			model.Timer.EnableFault<Timer.SuppressTimeout>();

			// Act
			simulator.Simulate(TimeSpan.FromHours(1));

			// Assert
			model.Tank.IsRuptured().Should().BeTrue();
		}
	}
}