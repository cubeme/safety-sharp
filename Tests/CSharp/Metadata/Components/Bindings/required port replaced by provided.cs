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

	internal abstract class X37 : TestComponent
	{
		public extern void M();
	}

	internal class X38 : X37
	{
		public X38()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private extern void N();

		public new void M()
		{
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(1);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });
		}
	}

	internal abstract class P37 : TestComponent
	{
		public extern int M { get; }
	}

	internal class P38 : P37
	{
		public P38()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private extern int N { get; }

		public new int M
		{
			get { return 1; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(1);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });
		}
	}
}