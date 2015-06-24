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

	internal class C17 : SemanticEqualityComponent
	{
		[Test(16)]
		public int M1(int a)
		{
			switch (a)
			{
			}

			return a;
		}

		[Test(16)]
		public int M2(ref int a)
		{
			switch (++a)
			{
				default:
					++a;
					return a;
			}
		}

		[Test(16)]
		public int M3(ref int a)
		{
			switch (++a)
			{
				case 1:
					a += 1;
					return 17;
				case 2:
					return 33;
			}

			return 48;
		}

		[Test(16)]
		public int M4(ref int a)
		{
			switch (++a)
			{
				case 1:
					return 17;
				case 2:
					--a;
					return 33;
				case 3:
				case 4:
				case 5:
					++a;
					return 177;
				case 31:
					return 18;
				default:
					return 77;
			}
		}

		//[Test(16)]
		//public int M4(int a)
		//{
		//	switch (++a)
		//	{
		//		case 1:
		//			a = 17;
		//			break;
		//		case 2:
		//			a = 19;
		//			break;
		//	}

		//	return a;
		//}

		//[Test(16)]
		//public int M5(int a)
		//{
		//	switch (++a)
		//	{
		//		case 1:
		//		{
		//			var x = a + 1;
		//			a = 17 - x;
		//			break;
		//		}
		//		case 2:
		//		{
		//			var x = a == 2;
		//			a = x ? 19 : 17;
		//			break;
		//		}
		//	}

		//	return a;
		//}

		//[Test(16)]
		//public int M6(int a)
		//{
		//	switch (++a)
		//	{
		//		case 1:
		//			a = 17;
		//			break;
		//		case 2:
		//			a = 19;
		//			break;
		//		default:
		//			a = 21;
		//			break;
		//	}

		//	return a;
		//}

		//[Test(16)]
		//public int M7(int a)
		//{
		//	switch (++a)
		//	{
		//		default:
		//			a = 21;
		//			break;
		//		case 1:
		//			a = 17;
		//			break;
		//		case 2:
		//			a = 19;
		//			break;
		//	}

		//	return a;
		//}

		//[Test(16)]
		//public int M8(int a)
		//{
		//	switch (++a)
		//	{
		//		case 23:
		//		default:
		//		case 73:
		//			a = 21;
		//			break;
		//		case 1:
		//		case 17:
		//		case 43:
		//		case 29:
		//			a = 17;
		//			break;
		//		case 2:
		//			a = 19;
		//			break;
		//	}

		//	return a;
		//}
	}
}