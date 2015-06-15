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
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X10 : TestComponent
	{
		public virtual void M()
		{
		}
	}

	internal class X11 : X10
	{
		private extern void N();

		public override void M()
		{
		}

		public X11()
		{
			Bind(RequiredPorts.N = base.ProvidedPorts.M);
		}

		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(4);

			Metadata.ProvidedPorts[0].Method.ShouldBe(typeof(X10).GetMethod("M"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");

			Metadata.ProvidedPorts[1].Method.ShouldBe(typeof(X11).GetMethod("M"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(typeof(X10).GetMethod("M"));
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");

			Metadata.ProvidedPorts[2].Method.ShouldBe(typeof(X11).GetMethod("Check", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[2].Name.ShouldBe("Check");

			Metadata.ProvidedPorts[3].Method.ShouldBe(typeof(X11).GetMethod("__SynthesizedPort0__", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.ProvidedPorts[3].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[3].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[3].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[3].Name.ShouldBe("__SynthesizedPort0__");
			Metadata.ProvidedPorts[3].CanBeAffectedByFaultEffects.ShouldBe(true);
			Metadata.ProvidedPorts[3].HasImplementation.ShouldBe(true);
			Metadata.ProvidedPorts[3].Implementation.ShouldBe(typeof(X11).GetMethod("__Behavior4__",
				BindingFlags.Instance | BindingFlags.NonPublic));
		}
	}
}