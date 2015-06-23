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

	internal class C11 : SemanticEqualityComponent
	{
		private int F(int a)
		{
			return a;
		}

		private void F(ref int a)
		{
			a = a + 1;
		}

		private int G(int a)
		{
			return a;
		}

		private bool G(bool a)
		{
			return a;
		}

		private double G(double a)
		{
			return a;
		}

		[Test(4)]
		public void M1(ref int a)
		{
			a = F(a);
		}

		[Test(1)]
		public void M2(ref int a)
		{
			F(ref a);
		}

		[Test(4)]
		public int M3(int a)
		{
			return G(a);
		}

		[Test(1)]
		public bool M4(bool a)
		{
			return G(a);
		}

		[Test(4)]
		public double M5(double a)
		{
			return G(a);
		}
	}
}