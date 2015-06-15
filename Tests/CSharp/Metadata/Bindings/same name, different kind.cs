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

namespace Tests.Metadata.Bindings
{
	using System;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X23 : TestComponent
	{
		public X23()
		{
			Bind(RequiredPorts.M = ProvidedPorts.N);
		}

		private void M()
		{
		}

		private extern void N();

		private void N(int i)
		{
		}

		private extern void M(int i);

		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(1);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });
			Metadata.ProvidedPorts[1].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });
		}
	}

	internal class X24 : TestComponent
	{
		public X24()
		{
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		private void M()
		{
		}

		private extern void N();

		private void N(int i)
		{
		}

		private extern void M(int i);

		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(1);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[0] });
			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}
}