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

namespace Tests.Metadata.Diagnostics.Bindings.Valid
{
	using System;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class M5 : TestModel
	{
		public M5()
		{
			var z = new Z();
			AddRootComponents(new Y(new X(z), z));
		}

		protected override void Check()
		{
			Metadata.RootComponent.Subcomponents[0].Bindings.Length.ShouldBe(1);
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
			private X x;

			public Y(X x, Z z)
			{
				this.x = x;
				Bind(RequiredPorts.M = z.ProvidedPorts.N);
			}

			private extern void M();
		}
	}

	internal class M6 : TestModel
	{
		public M6()
		{
			var z = new Z();
			AddRootComponents(new Y(new X(z), z));
		}

		protected override void Check()
		{
			Metadata.RootComponent.Subcomponents[0].Bindings.Length.ShouldBe(1);
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
			private X x;

			public Y(X x, Z z)
			{
				this.x = x;
				Bind(z.RequiredPorts.N = ProvidedPorts.M);
			}

			private void M()
			{
			}
		}
	}
}