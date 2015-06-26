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
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal interface I3 : IComponent
	{
		[Required]
		int P { get; }

		[Provided]
		void M();
	}

	internal class X45 : Component, I3
	{
		public virtual void M()
		{
		}

		public virtual int P { get { return 1; } }
	}

	internal class X47 : X45
	{
		public override int P
		{
			get { return base.P; }
		}

		public override void M()
		{
		}
	}

	internal class X48 : TestComponent
	{
		private readonly I3 _i = new X47();

		public X48()
		{
			Bind(RequiredPorts.N = _i.ProvidedPorts.M);
			Bind(RequiredPorts.Q = _i.ProvidedPorts.P);
		}

		private extern int Q { get; }
		public extern void N();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Bindings.Length.ShouldBe(2);

			Metadata.Bindings[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(((Component)_i).GetMetadata().ProvidedPorts[3]);

			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { ((Component)_i).GetMetadata().ProvidedPorts[3] });
			((Component)_i).GetMetadata().ProvidedPorts[3].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[1] });

			Metadata.Bindings[1].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Bindings[1].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[1].ProvidedPort.ShouldBe(((Component)_i).GetMetadata().ProvidedPorts[2]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { ((Component)_i).GetMetadata().ProvidedPorts[2] });
			((Component)_i).GetMetadata().ProvidedPorts[2].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0] });
		}
	}
}