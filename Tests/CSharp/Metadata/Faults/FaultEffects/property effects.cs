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
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	public class X2 : TestComponent
	{
		public int M
		{
			get { return 1; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F).GetMethod("get_M"));
			Metadata.Faults[0].Effects[0].Name.ShouldBe("get_M");
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F).GetMethod("get_M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(0);

			Metadata.ProvidedPorts[0].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0] });
		}

		[Transient]
		private class F : Fault
		{
			public int M
			{
				get { return 2; }
			}
		}
	}

	public class X2b : TestComponent
	{
		public int M
		{
			set { }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Effects.Length.ShouldBe(1);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F).GetMethod("set_M"));
			Metadata.Faults[0].Effects[0].Name.ShouldBe("set_M");
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F).GetMethod("set_M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(0);

			Metadata.ProvidedPorts[0].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0] });
		}

		[Transient]
		private class F : Fault
		{
			public int M
			{
				set { }
			}
		}
	}

	public class X2c : TestComponent
	{
		public int M
		{
			get { return 1; }
			set { }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Effects.Length.ShouldBe(2);

			Metadata.Faults[0].Effects[0].MethodInfo.ShouldBe(typeof(F).GetMethod("get_M"));
			Metadata.Faults[0].Effects[0].Name.ShouldBe("get_M");
			Metadata.Faults[0].Effects[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[0].IntendedBehavior.ShouldBe(typeof(F).GetMethod("get_M"));
			Metadata.Faults[0].Effects[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[0].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[0].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.Faults[0].Effects[0].Priority.ShouldBe(0);

			Metadata.Faults[0].Effects[1].MethodInfo.ShouldBe(typeof(F).GetMethod("set_M"));
			Metadata.Faults[0].Effects[1].Name.ShouldBe("set_M");
			Metadata.Faults[0].Effects[1].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].Effects[1].IntendedBehavior.ShouldBe(typeof(F).GetMethod("set_M"));
			Metadata.Faults[0].Effects[1].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[1].IsAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].Effects[1].FaultEffects.ShouldBeEmpty();
			Metadata.Faults[0].Effects[1].AffectedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.Faults[0].Effects[1].Priority.ShouldBe(0);

			Metadata.ProvidedPorts[0].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[0] });
			Metadata.ProvidedPorts[1].FaultEffects.ShouldBe(new[] { Metadata.Faults[0].Effects[1] });
		}

		[Transient]
		private class F : Fault
		{
			public int M
			{
				get { return 2; }
				set { }
			}
		}
	}
}