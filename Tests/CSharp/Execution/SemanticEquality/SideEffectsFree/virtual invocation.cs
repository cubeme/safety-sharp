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

	internal abstract class C19 : SemanticEqualityComponent
	{
		protected virtual int P
		{
			get { return 17; }
		}

		protected virtual int M(int i)
		{
			return i;
		}
	}

	internal class C20 : C19
	{
		protected override int P
		{
			get { return base.P - 2; }
		}

		protected override int M(int i)
		{
			return base.M(i) * 3;
		}

		[Test(16)]
		public int M1(int x)
		{
			return M(x);
		}

		[Test(16)]
		public int M2(int x)
		{
			return base.M(x);
		}

		[Test(1)]
		public int M3()
		{
			return P;
		}

		[Test(1)]
		public int M4()
		{
			return base.P;
		}
	}
}