﻿namespace Elbtunnel
{
	using System;
	using System.Linq.Expressions;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		private class Elbtunnel : Model
		{
			public Elbtunnel(bool nondeterministicInitialValue)
			{
				var c1 = new BooleanComponent(nondeterministicInitialValue);
				var c2 = new BooleanComponent(false);
				var lb = new LightBarrier();
				var t = new Test2();
				SetPartitions(c1, c2, t, lb);

				var unknown = new LightBarrier();
				var value = c1.Access<bool>("_value");
				var value1 = lb.Access<int>("i");
				var value2 = c1.Access<bool>("_value");

				bool b = value;
				int x = 0;
				Hazard = Ltl.Globally(value != b || -value1 == x)
							.Implies(Ltl.Finally(!value == false || value2 == true || lb.Triggered && t.boolean2._value));

				Hazard2 = Ctl.AllPaths.Globally(value != false || unknown.Triggered);
			}

			public LtlFormula Hazard { get; private set; }
			public CtlFormula Hazard2 { get; private set; }
		}

		private static void Main(string[] args)
		{
			var elbtunnel = new Elbtunnel(true);
			var spin = new SpinModelChecker(elbtunnel);

			spin.Check(elbtunnel.Hazard);
		}

		[Test]
		public void FirstTest()
		{
			var elbtunnel = new Elbtunnel(true);
			var spin = new SpinModelChecker(elbtunnel);

			spin.Check(elbtunnel.Hazard);
		}
	}
}