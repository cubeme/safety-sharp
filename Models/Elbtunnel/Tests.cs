namespace Elbtunnel
{
	using System;
	using NUnit.Framework;
	using SafetySharp.Modeling;
	using SharedComponents;

	[TestFixture]
	public class Tests
	{
		// Model non-abstract? Model config in test's SetUp method?
		private class Elbtunnel : Model
		{
			public Elbtunnel(bool nondeterministicInitialValue)
			{
				var c1 = new BooleanComponent(nondeterministicInitialValue);
				var c2 = new BooleanComponent(false);
				var timer = new Timer(20);
				var lb = new LightBarrier(timer);
				var t = new Test2();
				SetRootComponents(new InterfacedSubcomponent(new LightBarrier(timer)), new Timer(70));

				//var unknown = new LightBarrier();
				//var value = c1.Access<bool>("Value");
				//var value1 = lb.Access<int>("_i");
				//var value2 = c1.Access<bool>("Value");

				//bool b = value;
				//var x = 0;
				// Hazard = Ltl.Globally(value != b
				// 					  || -value1 == x
				// 					  || c1.Lane == Lane.Right)
				// 			.Implies(Ltl.Finally(!value == false || value2 == true || lb.Triggered && t.Boolean2.Value));
				// 
				// Hazard2 = Ctl.AllPaths.Globally(value != false || unknown.Triggered);

				//Hazard = Ltl($"{value} != {b} || F !{value} <-> {lb}.Triggered -> {lb.Triggered}");
				// G {lb}.Triggered -> G $lb_triggered
				// G {lb.Triggered} -> G false
				// allowed in holes: components, component member accesses for constants/readonly fields, int/bool constants or vars
				// {lb.Triggered} should be forbidden _unless_ Triggered is const, a readonly/immutable field or property
			}

			//public LtlFormula Hazard { get; private set; }
			//public CtlFormula Hazard2 { get; private set; }
		}

		private static void Main(string[] args)
		{
			var elbtunnel = new Elbtunnel(true);
			var spin = new SpinModelChecker(elbtunnel);

			//spin.Check(Ltl.Globally(true));
		}

		[Test] 
		public void FirstTest()
		{
			var elbtunnel = new Elbtunnel(true);
			var spin = new SpinModelChecker(elbtunnel);

			//spin.Check(elbtunnel.Hazard);
		}
	}
}