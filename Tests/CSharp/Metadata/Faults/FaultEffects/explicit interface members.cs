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

	interface I2 : IComponent
	{
		[Provided]
		void M();
	}

	public class X2 : TestComponent, I2
	{
		void I2.M()
		{
		}

		protected override void Check()
		{
			Metadata.Faults[0].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F).GetMethod("M"));
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F).GetMethod("M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].AffectingFaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(0);

			Metadata.ProvidedPorts[0].AffectingFaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0] });
		}

		[Transient]
		private class F : Fault
		{
			public void M()
			{
			}
		}
	}

	interface I3 : IComponent
	{
		[Required]
		void M();
	}

	public class X3 : TestComponent, I3
	{
		extern void I3.M();

		protected override void Check()
		{
			Metadata.Faults[0].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F).GetMethod("M"));
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F).GetMethod("M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].AffectingFaultEffects.ShouldBe(new FaultEffectMetadata[] { });
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(0);

			Metadata.RequiredPorts[0].AffectingFaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0] });
		}

		[Transient]
		private class F : Fault
		{
			public void M()
			{
			}
		}
	}
}