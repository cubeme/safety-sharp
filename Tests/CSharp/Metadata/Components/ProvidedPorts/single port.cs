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

namespace Tests.Metadata.Components.ProvidedPorts
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X2 : TestComponent
	{
		private void M()
		{
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(1);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X2).GetMethod("M", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].IntendedBehavior.ShouldBe(typeof(X2).GetMethod("__Behavior0__",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");
		}
	}

	internal class P2a : TestComponent
	{
		private int P
		{
			get { return 1; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(1);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(P2a).GetMethod("get_P", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].IntendedBehavior.ShouldBe(typeof(P2a).GetMethod("__Behavior0__",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");
		}
	}

	internal class P2b : TestComponent
	{
		private int P
		{
			set { }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(1);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(P2b).GetMethod("set_P", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].IntendedBehavior.ShouldBe(typeof(P2b).GetMethod("__Behavior0__",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].Name.ShouldBe("set_P");
		}
	}

	internal class P2c : TestComponent
	{
		private int P { get; set; }

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(2);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(P2a).GetMethod("get_P", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[0].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].IntendedBehavior.ShouldBe(typeof(P2a).GetMethod("__Behavior0__",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[0].Name.ShouldBe("get_P");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(P2b).GetMethod("set_P", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[1].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[1].IntendedBehavior.ShouldBe(typeof(P2b).GetMethod("__Behavior1__",
				BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[1].Name.ShouldBe("set_P");
		}
	}
}