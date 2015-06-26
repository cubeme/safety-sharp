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

namespace Tests.Execution.SemanticEquality.SideEffectsFree
{
	using System;
	using SafetySharp.Modeling;

	internal interface I4 : IComponent
	{
		[Provided]
		bool F { get; }

		[Provided]
		int G { get; }
	}

	internal class C22 : SemanticEqualityComponent
	{
		private readonly I4 _c1 = new C1();
		private readonly I4 _c2 = new C2();

		[Test(1)]
		public bool M1()
		{
			return _c1.F;
		}

		[Test(1)]
		public int M2()
		{
			return _c1.G;
		}

		[Test(1)]
		public bool M3()
		{
			return _c2.F;
		}

		[Test(1)]
		public int M4()
		{
			return _c2.G;
		}

		private class C1 : Component, I4
		{
			bool I4.F
			{
				get { return false; }
			}

			public virtual int G
			{
				get { return 99; }
			}
		}

		private class C2 : C1, I4
		{
			int I4.G
			{
				get { return base.G / 2; }
			}
		}
	}
}