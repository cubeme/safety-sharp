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

namespace Tests.Metadata.Diagnostics.Bindings.Invalid
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.MetadataAnalyzers;
	using Shouldly;
	using Utilities;

	internal class T1 : TestObject
	{
		protected override void Check()
		{
			var z = new Z();
			var m = new Model();
			m.AddRootComponents(new X(z), new Y(z));

			Tests.RaisesWith<InvalidBindingException>(() => m.Seal(),
				e => e.Binding.ShouldBe(m.Metadata.RootComponent.Subcomponents[1].Bindings[0]));
		}

		private class Z : Component
		{
			public void N()
			{
			}
		}

		private class X : Component
		{
			private Z z;

			public X(Z z)
			{
				this.z = z;
			}
		}

		private class Y : Component
		{
			public Y(Z z)
			{
				Bind(RequiredPorts.M = z.ProvidedPorts.N);
			}

			private extern void M();
		}
	}

	internal class T1b : TestObject
	{
		protected override void Check()
		{
			var z = new Z();
			var m = new Model();
			m.AddRootComponents(new X(z), new Y(z));

			Tests.RaisesWith<InvalidBindingException>(() => m.Seal(),
				e => e.Binding.ShouldBe(m.Metadata.RootComponent.Subcomponents[1].Bindings[0]));
		}

		private class Z : Component
		{
			public int N
			{
				set { }
			}
		}

		private class X : Component
		{
			private Z z;

			public X(Z z)
			{
				this.z = z;
			}
		}

		private class Y : Component
		{
			public Y(Z z)
			{
				Bind(RequiredPorts.M = z.ProvidedPorts.N);
			}

			private extern int M { set; }
		}
	}

	internal class T2 : TestObject
	{
		protected override void Check()
		{
			var z = new Z();
			var m = new Model();
			m.AddRootComponents(new X(z), new Y(z));

			Tests.RaisesWith<InvalidBindingException>(() => m.Seal(),
				e => e.Binding.ShouldBe(m.Metadata.RootComponent.Subcomponents[1].Bindings[0]));
		}

		private class Z : Component
		{
			public extern void N();
		}

		private class X : Component
		{
			private Z z;

			public X(Z z)
			{
				this.z = z;
			}
		}

		private class Y : Component
		{
			public Y(Z z)
			{
				Bind(z.RequiredPorts.N = ProvidedPorts.M);
			}

			private void M()
			{
			}
		}
	}
}