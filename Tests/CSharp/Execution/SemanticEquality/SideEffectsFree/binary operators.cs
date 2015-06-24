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

	internal class C5 : SemanticEqualityComponent
	{
		[Test(16)]
		public int M1(int a, int b)
		{
			return a + b;
		}

		[Test(16)]
		public int M2(int a, int b)
		{
			return a - b;
		}

		[Test(16)]
		public int M3(int a, int b)
		{
			return a * b;
		}

		[Test(16)]
		public int M4(int a, int b)
		{
			return a / (b == 0 ? 1 : b);
		}

		[Test(16)]
		public int M5(int a, int b)
		{
			return a % (b == 0 ? 1 : b);
		}

		[Test(4)]
		public bool M6(bool a, bool b)
		{
			return a & b;
		}

		[Test(4)]
		public bool M7(bool a, bool b)
		{
			return a | b;
		}

		[Test(16)]
		public bool M8(int a, int b)
		{
			return a == b;
		}

		[Test(16)]
		public bool M9(int a, int b)
		{
			return a != b;
		}

		[Test(16)]
		public bool M10(int a, int b)
		{
			return a < b;
		}

		[Test(16)]
		public bool M11(int a, int b)
		{
			return a <= b;
		}

		[Test(16)]
		public bool M12(int a, int b)
		{
			return a > b;
		}

		[Test(16)]
		public bool M13(int a, int b)
		{
			return a >= b;
		}

		[Test(4)]
		public bool M14(bool a, bool b)
		{
			return a && b;
		}

		[Test(4)]
		public bool M15(bool a, bool b)
		{
			return a || b;
		}

		[Test(32)]
		public bool M16(int a, int b, bool c)
		{
			return a + 1 > b * 2 - 1 & !c;
		}

		[Test(16)]
		public int M17(ref int a, int b)
		{
			a += b;
			return a;
		}

		[Test(16)]
		public int M18(ref int a, int b)
		{
			a -= b;
			return a;
		}

		[Test(16)]
		public int M19(ref int a, int b)
		{
			a *= b;
			return a;
		}

		[Test(16)]
		public int M20(ref int a, int b)
		{
			a /= (b == 0 ? 1 : b);
			return a;
		}

		[Test(16)]
		public int M21(ref int a, int b)
		{
			a %= (b == 0 ? 1 : b);
			return a;
		}

		[Test(4)]
		public bool M22(ref bool a, bool b)
		{
			a &= b;
			return a;
		}

		[Test(4)]
		public bool M23(ref bool a, bool b)
		{
			a |= b;
			return a;
		}

		[Test(1)]
		public bool M24()
		{
			return X.A == X.B;
		}

		[Test(1)]
		public bool M25()
		{
			return X.A != X.B;
		}

		private enum X
		{
			A,
			B,
			C
		}
	}
}