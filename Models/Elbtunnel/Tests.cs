namespace Elbtunnel
{
	using System;
	using System.Linq.Expressions;
	using NUnit.Framework;
	using SafetySharp.Modeling;

	[TestFixture]
	public class Tests
	{
		private class PropertyPattern : Formula
		{
			protected Formula Formula;
		}

		private class GloballyProperty : PropertyPattern
		{
			public GloballyProperty(Expression<Func<bool>> expr)
			{
				Formula = Ltl.Globally(expr);
			}
		}

		private class Configuration : ModelConfiguration
		{
			public Configuration(bool nondeterministicInitialValue)
			{
				var c1 = new BooleanComponent(nondeterministicInitialValue);
				var c2 = new BooleanComponent(false);
				var lb = new LightBarrier();

				AddPartitions(c1, c2, new Test2());

				// Non-string version
				//Hazard = Ltl.Globally(() => c1.AccessInternal<bool>("_value") == false);
				//Hazard = Ltl.Globally(Ltl.AccessInternalsOf(c1)._value == false);
				//Hazard = Ltl.Implies(Ltl.Globally(c1.AccessInternal<bool>("_value")), Ltl.Globally(c1.AccessInternal<bool>("_value")));
				//// "(G $0._value) => (G $0._value)"
				////Hazard = Ltl.Globally(() => lb.Triggered);
				//Hazard = Ltl.AccessInternalsOf(c1)._value == false;
				//Hazard = Ltl.StateFormula(c1.AccessInternal<bool>(c => c._value) == false);

				//dynamic q = c1;
				//q._value = 3;
				//Hazard = Ltl.Globally("c1._value == false", Tuple.Create("c1", c1));

				// Shorter version that depends on automatic lambda lifting of parameter
				//Hazard = Ltl.Globally(c1.AccessInternal<bool>("_value") == false);
				//Hazard = Ltl.Globally(lb.Triggered);

				Hazard = new GloballyProperty(() => c1.AccessInternal<bool>(c => c._value) == false);
			}

			public Formula Hazard { get; private set; }
		}

		private static void Main(string[] args)
		{
			var spin = new SpinModelChecker(new Configuration(true));
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