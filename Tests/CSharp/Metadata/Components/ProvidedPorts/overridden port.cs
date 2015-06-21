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
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X8 : TestComponent
	{
		public void M()
		{
		}

		public virtual bool M(ref int i)
		{
			return i == 2;
		}

		public abstract bool N(out bool i);
	}

	internal abstract class X9 : X8
	{
		public override bool M(ref int i)
		{
			return false;
		}

		public override bool N(out bool i)
		{
			i = false;
			return true;
		}

		public int M(out bool i)
		{
			i = false;
			return 1;
		}
	}

	internal class X9b : X9
	{
		public override bool M(ref int i)
		{
			return false;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(6);

			Metadata.ProvidedPorts[0].MethodInfo.ReturnType.ShouldBe(typeof(void));
			Metadata.ProvidedPorts[0].MethodInfo.DeclaringType.ShouldBe(typeof(X8));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[0].OverridingMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[0]);
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");

			Metadata.ProvidedPorts[1].MethodInfo.ReturnType.ShouldBe(typeof(bool));
			Metadata.ProvidedPorts[1].MethodInfo.DeclaringType.ShouldBe(typeof(X8));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[1].OverridingMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[1].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[5]);
			Metadata.ProvidedPorts[1].Name.ShouldBe("M1");

			Metadata.ProvidedPorts[2].MethodInfo.ReturnType.ShouldBe(typeof(bool));
			Metadata.ProvidedPorts[2].MethodInfo.DeclaringType.ShouldBe(typeof(X9));
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(Metadata.ProvidedPorts[1]);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[2].IsOverridden.ShouldBe(true);
			Metadata.ProvidedPorts[2].OverridingMethod.ShouldBe(Metadata.ProvidedPorts[5]);
			Metadata.ProvidedPorts[2].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[5]);
			Metadata.ProvidedPorts[2].Name.ShouldBe("M2");

			Metadata.ProvidedPorts[3].MethodInfo.ShouldBe(typeof(X9).GetMethod("N"));
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[3].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[3].OverridingMethod.ShouldBe(null);
			Metadata.ProvidedPorts[3].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[3]);
			Metadata.ProvidedPorts[3].Name.ShouldBe("N");

			Metadata.ProvidedPorts[4].MethodInfo.ReturnType.ShouldBe(typeof(int));
			Metadata.ProvidedPorts[4].MethodInfo.DeclaringType.ShouldBe(typeof(X9));
			Metadata.ProvidedPorts[4].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[4].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[4].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[4].OverridingMethod.ShouldBe(null);
			Metadata.ProvidedPorts[4].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[4]);
			Metadata.ProvidedPorts[4].Name.ShouldBe("M3");

			Metadata.ProvidedPorts[5].MethodInfo.ReturnType.ShouldBe(typeof(bool));
			Metadata.ProvidedPorts[5].MethodInfo.DeclaringType.ShouldBe(typeof(X9b));
			Metadata.ProvidedPorts[5].BaseMethod.ShouldBe(Metadata.ProvidedPorts[2]);
			Metadata.ProvidedPorts[5].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[5].IsOverridden.ShouldBe(false);
			Metadata.ProvidedPorts[5].OverridingMethod.ShouldBe(null);
			Metadata.ProvidedPorts[5].VirtuallyInvokedMethod.ShouldBe(Metadata.ProvidedPorts[5]);
			Metadata.ProvidedPorts[5].Name.ShouldBe("M4");
		}
	}
}