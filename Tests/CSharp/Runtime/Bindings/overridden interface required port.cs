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
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;

	internal interface I4 : IComponent
	{
		[Required]
		void M();
	}

	internal class X49 : Component, I4
	{
		public virtual extern void M();
	}

	internal class X50 : X49, I4
	{
		public override extern void M();
	}

	internal class X51 : TestComponent
	{
		private readonly I4 _i = new X50();

		public X51()
		{
			Bind(_i.RequiredPorts.M = ProvidedPorts.N);
		}

		public void N()
		{
		}

		protected override void Check()
		{
			Metadata.Bindings.Count().ShouldBe(1);

			Metadata.Bindings[0].Component.Component.ShouldBe(this);
			Metadata.Bindings[0].RequiredPort.ShouldBe(_i.GetComponentInfo().RequiredPorts[1]);
			Metadata.Bindings[0].ProvidedPort.ShouldBe(Metadata.ProvidedPorts[0]);
		}
	}
}