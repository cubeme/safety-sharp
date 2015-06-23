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
	using SafetySharp.Modeling;

	internal class C3 : SemanticEqualityComponent
	{
		private readonly Q q = new Q();
		private int _f1;

		[Test(32)]
		public int M1(int x)
		{
			F5();
			return _f1 + x;
		}

		[Test(32)]
		public int M2(int x)
		{
			_f1 = x + 2;
			return F1(x);
		}

		[Test(32)]
		public int M3(int x)
		{
			_f1 += _f1 > 0 ? F2(2) : F2(1);
			return _f1;
		}

		[Test(32)]
		public int M4(int x, int y)
		{
			F3(ref x, out y);
			return x + y;
		}

		[Test(32)]
		public int M5(ref int x, ref int y)
		{
			F4(ref x, out y);
			return x + y;
		}

		[Test(32)]
		public int M6(int x)
		{
			int y = x;
			int z = x + 1;
			F4(ref y, out z);
			return z + x + y;
		}

		[Test(32)]
		public int M7(int x)
		{
			return x + x > 0 ? q.M(ref x) + q.M(ref x) : q.M(ref x) - q.M(ref x);
		}

		[Test(32)]
		public void M8(int x, int y)
		{
			if (x == y)
				return;
			_f1 = x;
		}

		[Test(32)]
		public int M9(ref int x)
		{
			return x;
		}

		[Test(32)]
		public int M10(ref int x)
		{
			x = 17;
			return x;
		}

		private int F1(int x)
		{
			return x + _f1;
		}

		private int F2(int x)
		{
			return x + (_f1 += 1);
		}

		private void F3(ref int x, out int y)
		{
			x = x + 1;
			y = x;
		}

		private void F4(ref int x, out int y)
		{
			x = x + 1;
			y = x;
		}

		private void F5()
		{
			_f1 = 3;
		}

		private class Q : Component
		{
			public int M(ref int x)
			{
				return x++;
			}
		}
	}
}