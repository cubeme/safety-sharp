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

	internal class C5 : Component
	{
		public extern void M();
	}

	internal class C6 : Component
	{
		public void N()
		{
		}
	}

	internal class T4 : TestObject
	{
		protected override void Check()
		{
			var c1 = new C5();
			var c2 = new C6();
			var c3 = new C6();
			var m = new Model();

			m.AddRootComponents(c2, c1, c3);
			m.Bind(c1.RequiredPorts.M = c2.ProvidedPorts.N);
			m.Bind(c1.RequiredPorts.M = c3.ProvidedPorts.N);

			Tests.RaisesWith<AmbiguousBindingsException>(() => m.Seal(),
				e => e.RequiredPort.ShouldBe(m.Metadata.RootComponent.Subcomponents[1].RequiredPorts[0]));
		}
	}
}