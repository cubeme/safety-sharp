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

namespace Tests.Execution.SemanticEquality.SideEffects
{
	using System;

	// =============================================================================================
	// Generated variables are called t with a numeric prefix; some of these tests ensure that we 
	// don't mix up those variables with other symbols called t
	// =============================================================================================

	internal class C6 : SemanticEqualityComponent
	{
		private int t;

		[Test(32)]
		public int M1(int x)
		{
			if ((x += 2) > 0 || --x == (t = x + 1))
				return 0;

			return t;
		}
	}

	internal class C7 : SemanticEqualityComponent
	{
		private int t(int x)
		{
			return x * x;
		}

		[Test(32)]
		public int M1(int x)
		{
			if ((x += 2) > 0 || --x == t(x))
				return 0;

			return t(x - 2);
		}
	}

	internal class C8 : SemanticEqualityComponent
	{
		[Test(32)]
		public int M1(int x)
		{
			int t = x + 1, t1 = x, t2 = x - 1;

			if ((x += 2) > 0 || --x == (t1 = x + 1) && (t1 += 2) > (t2 -= 1))
				return t2;

			return t;
		}
	}

	internal class C9 : SemanticEqualityComponent
	{
		[Test(32)]
		public int M1(int x)
		{
			var y = x++ > 0 || x-- < 0;
			return y ? x + 1 : x - 1;
		}
	}

	internal abstract class C10 : SemanticEqualityComponent
	{
		protected int t(int x)
		{
			return x * x;
		}
	}

	internal class C11 : C10
	{
		[Test(32)]
		public int M1(int x)
		{
			if ((x += 2) > 0 || --x == t(x))
				return 0;

			return t(x - 2);
		}
	}
}