﻿// The MIT License (MIT)
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
	using SafetySharp.Runtime;
	using Shouldly;

	internal abstract class X27 : TestComponent
	{
		protected X27()
		{
			Bind(RequiredPorts.Q = ProvidedPorts.M);
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
			Bind(RequiredPorts.N = ProvidedPorts.M);
		}

		public extern void N();

		public override void M()
		{
		}

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(2);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(Metadata.RequiredPorts[0]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.Bindings[1].Component.Component.ShouldBe(this);
			Metadata.Bindings[1].RequiredPort.ShouldBe(Metadata.RequiredPorts[1]);
			Metadata.Bindings[1].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[1]);

			Metadata.RequiredPorts[0].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });
			Metadata.RequiredPorts[1].BoundProvidedPorts.ShouldBe(new[] { Metadata.ProvidedPorts[1] });

			Metadata.ProvidedPorts[0].BoundRequiredPorts.ShouldBe(new RequiredPortInfo[] { });
			Metadata.ProvidedPorts[1].BoundRequiredPorts.ShouldBe(new[] { Metadata.RequiredPorts[0], Metadata.RequiredPorts[1] });
		}
	}
}