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

	internal abstract class X27 : TestComponent
	{
		protected X27()
		{
			Bind(RequiredPorts.Q = ProvidedPorts.M);
			Bind(RequiredPorts.R1 = ProvidedPorts.P);
		}

		public extern int R1 { get; }
		public extern int R2 { get; }
		public extern int R3 { get; }

		public virtual int P
		{
			get { return 1; }
		}

		public extern void Q();

		public virtual void M()
		{
		}
	}

	internal class X28 : X27
	{
		public X28()
		{
			Bind(RequiredPorts.N1 = ProvidedPorts.M);
			Bind(RequiredPorts.R2 = ProvidedPorts.P);
			Bind(RequiredPorts.N2 = base.ProvidedPorts.M);
			Bind(RequiredPorts.R3 = base.ProvidedPorts.P);
		}

		public override int P
		{
			get { return base.P; }
		}

		public extern void N1();
		public extern void N2();

		public override void M()
		{
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(6);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[3]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.Bindings[1].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[1].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[1].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[2].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[2].RequiredPort.ShouldBe(Metadata.RequiredPorts[3]);
			Metadata.Bindings[2].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[3]);

			Metadata.Bindings[3].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[3].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[3].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[2]);

			Metadata.Bindings[4].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[4].RequiredPort.ShouldBe(Metadata.RequiredPorts[4]);
			Metadata.Bindings[4].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.Bindings[5].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[5].RequiredPort.ShouldBe(Metadata.RequiredPorts[2]);
			Metadata.Bindings[5].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[2] });
			Metadata.RequiredPorts[2].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });
			Metadata.RequiredPorts[3].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[3] });
			Metadata.RequiredPorts[4].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });

			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0], Metadata.RequiredPorts[4] });
			Metadata.ProvidedPorts[1].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[3], Metadata.RequiredPorts[2] });
			Metadata.ProvidedPorts[2].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[3] });
			Metadata.ProvidedPorts[3].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[3] });
		}
	}
}