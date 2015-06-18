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

namespace Tests.Metadata.Diagnostics.RequiredPorts
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.MetadataAnalyzers;
	using Shouldly;
	using Utilities;

	internal class C1 : Component
	{
		private extern void M();
	}

	internal class C3 : Component
	{
	}

	internal class C2 : Component
	{
		private C3 _c2 = new C3();
		private C1 _c1 = new C1();
	}

	internal class T1 : TestObject
	{
		protected override void Check()
		{
			var m = new Model();
			m.AddRootComponent(new C1());

			Tests.RaisesWith<UnboundRequiredPortException>(() => m.Seal(),
				e => e.RequiredPort.ShouldBe(m.Metadata.RootComponent.Subcomponents[0].RequiredPorts[0]));
		}
	}

	internal class T2 : TestObject
	{
		protected override void Check()
		{
			var m = new Model();
			m.AddRootComponent(new C2());

			Tests.RaisesWith<UnboundRequiredPortException>(() => m.Seal(),
				e => e.RequiredPort.ShouldBe(m.Metadata.RootComponent.Subcomponents[0].Subcomponents[1].RequiredPorts[0]));
		}
	}
}