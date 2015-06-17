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

namespace Tests.Metadata.Models.Components
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.MetadataAnalysis;
	using Shouldly;
	using Utilities;

	internal class C7 : Component
	{
		private X8 _a;
		private X8 _b;

		public C7(X8 a, X8 b)
		{
			_a = a;
			_b = b;
		}
	}

	internal class X8 : Component
	{
	}

	internal class M8 : TestObject
	{
		protected override void Check()
		{
			var b = new X8();
			var c = new C7(b, b);
			var m = new Model();
			m.AddRootComponents(c);

			Tests.RaisesWith<ComponentHierarchyException>(() => m.Seal(), e => e.Component.ShouldBe(b.Metadata));
		}
	}
}