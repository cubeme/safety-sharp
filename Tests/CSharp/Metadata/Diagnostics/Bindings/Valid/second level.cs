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

namespace Tests.Metadata.Diagnostics.Bindings.Valid
{
	using System;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class M7 : TestObject
	{
		protected override void Check()
		{
			var x1 = new X1();
			var x2 = new X2();
			var m = new Model();

			m.AddRootComponents(new X3(x1, x2));
			m.Bind(x1.RequiredPorts.M = x2.ProvidedPorts.M);
			m.Seal();

			m.Metadata.Bindings.Length.ShouldBe(1);
		}

		private class X1 : Component
		{
			public extern void M();
		}

		private class X2 : Component
		{
			public void M()
			{
			}
		}

		private class X3 : Component
		{
			private X1 _x1;
			private X2 _x2;

			public X3(X1 x1, X2 x2)
			{
				_x1 = x1;
				_x2 = x2;
			}
		}
	}
}