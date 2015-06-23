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

	internal class C16 : SemanticEqualityComponent
	{
		[Test(8)]
		public int M1(bool b)
		{
			var x = 0;
			if (b)
				x = 17;

			return x;
		}

		[Test(8)]
		public int M2(bool b)
		{
			int x;
			if (b)
				x = 17;
			else
				x = 22;

			return x;
		}

		[Test(8)]
		public int M3(bool b, bool c)
		{
			int x;
			if (b)
				x = 17;
			else
			{
				if (c)
					x = 44;
				else
					x = 21;
			}

			return x;
		}

		[Test(8)]
		public int M4(int i)
		{
			int x;
			if (i < 50)
				x = -1;
			else if (i > 40)
				x = 0;
			else
				x = 1;

			return x;
		}

		[Test(8)]
		public int M5(bool b, int i)
		{
			if (!b && i > 0)
				return 1;
			else
				return 0;
		}

		[Test(8)]
		public int M6(bool b, int i)
		{
			if (!b && i > 0)
				return 1;
				
			return 0;
		}

		[Test(8)]
		public int M7(bool b, int i)
		{
			if (!b || i > 0)
				return 1;
			else
				return 0;
		}

		[Test(8)]
		public int M8(bool b, int i)
		{
			if (!b || i > 0)
				return 1;
				
			return 0;
		}
	}
}