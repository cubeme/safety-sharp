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

namespace Tests.Metadata.Components.Bindings
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X33 : TestComponent
	{
		public extern void M1();
		public extern void M2();
		public extern void M3();
	}

	internal class X34 : X33
	{
		public X34()
		{
			Bind(RequiredPorts.M1 = ProvidedPorts.N);
			Bind(((X33)this).RequiredPorts.M2 = ProvidedPorts.N);
			Bind(base.RequiredPorts.M3 = ProvidedPorts.N);
		}

		private void N()
		{
		}

		public new extern void M1();
		public new extern void M2();
		public new extern void M3();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(3);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[3]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[1].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[1].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[1].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[2].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[2].RequiredPort.ShouldBe(Metadata.RequiredPorts[2]);
			Metadata.Bindings[2].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });
			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[2].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[3].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[4].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });
			Metadata.RequiredPorts[5].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });

			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(
				new[] { Metadata.RequiredPorts[3], Metadata.RequiredPorts[1], Metadata.RequiredPorts[2] });
		}
	}

	internal abstract class P33 : TestComponent
	{
		public extern int M1 { set; }
		public extern int M2 { set; }
		public extern int M3 { set; }
	}

	internal class P34 : P33
	{
		public P34()
		{
			Bind(RequiredPorts.M1 = ProvidedPorts.N);
			Bind(((P33)this).RequiredPorts.M2 = ProvidedPorts.N);
			Bind(base.RequiredPorts.M3 = ProvidedPorts.N);
		}

		private int N
		{
			get { return 1; }
		}

		public new extern int M1 { get; }
		public new extern int M2 { get; }
		public new extern int M3 { get; }

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(3);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[3]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[1].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[1].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[1].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[2].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[2].RequiredPort.ShouldBe(Metadata.RequiredPorts[2]);
			Metadata.Bindings[2].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });
			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[2].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[3].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[4].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });
			Metadata.RequiredPorts[5].BoundProvidedPorts.ShouldBe(new ProvidedPortMetadata[] { });

			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(
				new[] { Metadata.RequiredPorts[3], Metadata.RequiredPorts[1], Metadata.RequiredPorts[2] });
		}
	}
}