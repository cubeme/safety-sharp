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

	internal class C7 : SemanticEqualityComponent
	{
		[Test(16)]
		public int M1(int a)
		{
			var q = a + 1;
			var b = a > 0;

			return b | a < 7 ? q + 17 : a - 3;
		}

		[Test(16)]
		public int M2(int a)
		{
			int q;
			bool b;

			q = a + 1;
			b = a > 0;

			return b | a < 7 ? q + 17 : a - 3;
		}

		[Test(16)]
		public int M3(int a)
		{
			int q = a + 1, z = 4 + a;
			var b = a > 0;

			return b | a < z ? q + 17 : a - 3;
		}

		[Test(16)]
		public int M4(int a)
		{
			int q = a + 1, z;
			var b = a > 0;

			z = a * 2;
			return b | a < z ? q + 17 : a - 3;
		}
	}
}