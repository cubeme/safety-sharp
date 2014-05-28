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

		private class MyPattern : PropertyPattern
		{
			public MyPattern()
			{
				
			}
			public MyPattern(Expression<Func<bool>> left, Expression<Func<bool>> right)
			{
				//left.Implies(right);
			}

			public MyPattern(bool left, bool right)
			{
				//left.Implies(right);
			}

			public Formula Left { get; set; }
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

				//Hazard = new MyPattern(c1.AccessInternal<bool>("_value"), c1.AccessInternal<bool>("_value"));

				//Hazard = Ltl.Globally(c1.AccessInternal<bool>("_value")).Implies(Ltl.Globally(!c1.AccessInternal<bool>("_value")));

				Hazard = LTL("(G {c1._value}) => (G !{c1._value})");
				Hazard = LTL("(G {c1._value}) => (G {c1._value != false && true}) || G false");

				var value = c1.AccessInternal<bool>("value");
				Hazard = LTL("(G {value}) => (G !{value})"); // for internal fields when C# doesn't allow method calls in holes?

				Hazard = new Formula().AllowAccessTo(c1, c => c._value).Ltl("G {c._value} => (G !{c._value");

				Hazard = new MyPattern(lb.Triggered, lb.Triggered);

				Hazard = Ltl.Globally(value).Implies(Ltl.Globally(!value));
				Hazard = Ltl.Globally(lb.Triggered).Implies(Ltl.Globally(!lb.Triggered));

				Hazard = LTL("(G {lb.Triggered}) => (G !{lb.Triggered})");

				Ltl.SafetyProperty(lb.Triggered,)
				Hazard = new MyPattern
				{
					Left = lb.Triggered
				};
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