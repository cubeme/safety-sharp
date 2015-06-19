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

namespace Tests.Metadata.Faults.FaultEffects
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	public class X2 : TestComponent
	{
		public int M(ref int i)
		{
			return i;
		}

		protected override void Check()
		{
			Metadata.Faults.Length.ShouldBe(2);
			Metadata.Faults[0].Effects.Length.ShouldBe(1);
			Metadata.Faults[1].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F1).GetMethod("M"));
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F1).GetMethod("M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(3);

			Metadata.Faults[1].Effects[0].MethodInfo.ShouldBe(typeof(F2).GetMethod("M"));
			Metadata.Faults[1].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[1].Effects[0].IntendedBehavior.ShouldBe(typeof(F2).GetMethod("M"));
			Metadata.Faults[1].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[1].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[1].Effects[0].Priority.ShouldBe(7);

			Metadata.ProvidedPorts[0].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0], Metadata.Faults[1].Effects[0] });
		}

		[Transient]
		private class F1 : Fault
		{
			[Priority(3)]
			public int M(ref int i)
			{
				return i;
			}
		}

		[Transient]
		private class F2 : Fault
		{
			[Priority(7)]
			public int M(ref int i)
			{
				return i;
			}
		}
	}

	public class X3 : TestComponent
	{
		public extern int M(ref int i);

		protected override void Check()
		{
			Metadata.Faults.Length.ShouldBe(2);
			Metadata.Faults[0].Effects.Length.ShouldBe(1);
			Metadata.Faults[1].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F1).GetMethod("M"));
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F1).GetMethod("M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(3);

			Metadata.Faults[1].Effects[0].MethodInfo.ShouldBe(typeof(F2).GetMethod("M"));
			Metadata.Faults[1].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[1].Effects[0].IntendedBehavior.ShouldBe(typeof(F2).GetMethod("M"));
			Metadata.Faults[1].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[1].Effects[0].AffectedMethod.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Faults[1].Effects[0].Priority.ShouldBe(7);

			Metadata.RequiredPorts[0].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0], Metadata.Faults[1].Effects[0] });
		}

		[Transient]
		private class F1 : Fault
		{
			[Priority(3)]
			public int M(ref int i)
			{
				return i;
			}
		}

		[Transient]
		private class F2 : Fault
		{
			[Priority(7)]
			public int M(ref int i)
			{
				return i;
			}
		}
	}

	public class X4 : TestComponent
	{
		public override void Update()
		{
		}

		protected override void Check()
		{
			Metadata.Faults.Length.ShouldBe(2);
			Metadata.Faults[0].Effects.Length.ShouldBe(1);
			Metadata.Faults[1].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F1).GetMethod("Update"));
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F1).GetMethod("Update"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.StepMethods[1]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(31);

			Metadata.Faults[1].Effects[0].MethodInfo.ShouldBe(typeof(F2).GetMethod("Update"));
			Metadata.Faults[1].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[1].Effects[0].IntendedBehavior.ShouldBe(typeof(F2).GetMethod("Update"));
			Metadata.Faults[1].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[1].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[1].Effects[0].AffectedMethod.ShouldBe(Metadata.StepMethods[1]);
			Metadata.Faults[1].Effects[0].Priority.ShouldBe(-1);

			Metadata.StepMethods[1].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0], Metadata.Faults[1].Effects[0] });
		}

		[Transient]
		private class F1 : Fault
		{
			[Priority(31)]
			public void Update()
			{
			}
		}

		[Transient]
		private class F2 : Fault
		{
			[Priority(-1)]
			public void Update()
			{
			}
		}
	}
}