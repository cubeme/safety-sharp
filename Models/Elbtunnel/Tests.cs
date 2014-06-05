namespace Elbtunnel
{
	using System;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		private static class MyPatterns
		{
			public static LtlFormula MyPattern(bool left, bool right)
			{
				return null;
			}
		}

		private class Configuration : ModelConfiguration
		{
			public Configuration(bool nondeterministicInitialValue)
			{
				var c1 = new BooleanComponent(nondeterministicInitialValue);
				var c2 = new BooleanComponent(false);
				var lb = new LightBarrier();
				var t = new Test2();

				AddPartitions(c1, c2, t, lb);

				var value = c1.AccessInternal<bool>("_value");
				var value2 = c1.AccessInternal<int>("_value");

				Hazard = Ltl.Globally(value).Implies(Ltl.Globally(!value == false || value2 == 5 || lb.Triggered && t.boolean2._value));
				var f = Ltl.Next(true);
				//Hazard = Ltl.Globally(Ltl.StateExpression("{0}", value))
				//	.Implies(Ltl.Globally("!{0} == false || {1} == 5 || {2}.Triggered", value, value2, lb));

				//Hazard = Ltl.Globally(lb.Triggered).Implies(Ltl.Globally(!lb.Triggered));
				//Hazard = MyPatterns.MyPattern(
				//	left: value,
				//	right: !value);
			}

			public LtlFormula Hazard { get; private set; }
		}

		private static void Main(string[] args)
		{
			var configuration = new Configuration(true);
			var spin = new SpinModelChecker(configuration);

			spin.Check(configuration.Hazard);
		}

		[Test]
		public void FirstTest()
		{
			var configuration = new Configuration(true);
			var spin = new SpinModelChecker(configuration);
			
			spin.Check(configuration.Hazard);
		}
	}
}