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

namespace Tests.Runtime.Bindings
{
	using System;
	using System.Linq;
	using Shouldly;

	internal class X2 : TestComponent
	{
		public X2()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private extern void N();
		private extern void N(int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X3 : TestComponent
	{
		public X3()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}

		private extern void N();

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X4 : TestComponent
	{
		public X4()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M(int i)
		{
		}

		private extern void N();
		private extern void N(int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });
		}
	}

	internal class X5 : TestComponent
	{
		public X5()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}

		private extern void N(int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });
			Metadata.ProvidedPorts[1].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X6 : TestComponent
	{
		public X6()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(bool b)
		{
		}

		private extern void N();
		private extern void N(int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X7 : TestComponent
	{
		public X7()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(int i)
		{
		}

		private extern void N();
		private extern void N(bool b);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X8 : TestComponent
	{
		public X8()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private void M(ref bool b)
		{
		}

		private extern void N(ref bool b);
		private extern void N(int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });
			Metadata.ProvidedPorts[1].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}

	internal class X9 : TestComponent
	{
		public X9()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M(ref int i)
		{
		}

		private void M(int i)
		{
		}

		private extern void N();
		private extern void N(ref int i);

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });
		}
	}
}