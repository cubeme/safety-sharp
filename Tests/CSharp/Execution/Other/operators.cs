//// The MIT License (MIT)
//// 
//// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
//// 
//// Permission is hereby granted, free of charge, to any person obtaining a copy
//// of this software and associated documentation files (the "Software"), to deal
//// in the Software without restriction, including without limitation the rights
//// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//// copies of the Software, and to permit persons to whom the Software is
//// furnished to do so, subject to the following conditions:
//// 
//// The above copyright notice and this permission notice shall be included in
//// all copies or substantial portions of the Software.
//// 
//// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//// THE SOFTWARE.

//namespace Tests.Execution.SemanticEquality
//{
//	using System;

//	internal class T41 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			var y = x > 0 ? -1 : 1;
//			return y - 1;
//		}
//	}

//	internal class T42 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			var y = x + _f > 0 ? -1 : 1;
//			return y - 1 - _f;
//		}
//	}

//	internal class T43 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			return x > 0 ? ++y : 0;
//		}
//	}

//	internal class T44 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			return x > 0 ? y-- : 0;
//		}
//	}

//	internal class T45 : TwoValParams
//	{
//		protected override int Execute(int s, int t)
//		{
//			var b = s > 0;
//			var c = t < 0;
//			var x = 1 + (b ? (c ? 4 : 2) : 3);
//			return x;
//		}
//	}

//	internal class T46 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			if (x > 0 || y > 0)
//				return -1;
//			return 0;
//		}
//	}

//	internal class T47 : TwoValParams
//	{
//		protected override int Execute(int q, int y)
//		{
//			var x = q > 2;
//			_f1 = y;
//			if (x || _f1 < 1)
//				return -1;
//			return 0;
//		}
//	}

//	internal class T48 : TwoOtherParams
//	{
//		protected override bool Execute(ref bool x, int y)
//		{
//			if (x && y < 0)
//				return false;

//			x = true;
//			return y > 0;
//		}
//	}
//}