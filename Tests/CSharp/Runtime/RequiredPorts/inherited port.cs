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

namespace Tests.Runtime.RequiredPorts
{
	using System;
	using System.Linq;
	using Shouldly;

	internal abstract class X4 : TestComponent
	{
		public extern bool M(ref int i);
	}

	internal class X5 : X4
	{
		public extern void Q(out int i);

		protected override void Check()
		{
			Metadata.RequiredPorts.Count().ShouldBe(2);

			Metadata.RequiredPorts[0].Method.ShouldBe(typeof(X4).GetMethod("M"));
			Metadata.RequiredPorts[0].Component.Component.ShouldBe(this);
			Metadata.RequiredPorts[0].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[0].CreateBody.ShouldBe(null);
			Metadata.RequiredPorts[0].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[0].Name.ShouldBe("M");

			Metadata.RequiredPorts[1].Method.ShouldBe(typeof(X5).GetMethod("Q"));
			Metadata.RequiredPorts[1].Component.Component.ShouldBe(this);
			Metadata.RequiredPorts[1].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[1].CreateBody.ShouldBe(null);
			Metadata.RequiredPorts[1].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[1].Name.ShouldBe("Q");
		}
	}
}