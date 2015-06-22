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

//	internal class T24 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			F();
//			return _f + x;
//		}

//		private void F()
//		{
//			_f = 3;
//		}
//	}

//	internal class T25 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			_f = x + 2;
//			return F(x);
//		}

//		private int F(int x)
//		{
//			return x + _f;
//		}
//	}

//	internal class T26 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			_f += _f > 0 ? F(2) : F(1);
//			return _f;
//		}

//		private int F(int x)
//		{
//			return x + (_f += 1);
//		}
//	}

//	internal class T27 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			F(ref x, out y);
//			return x + y;
//		}

//		private void F(ref int x, out int y)
//		{
//			x = x + 1;
//			y = x;
//		}
//	}

//	internal class T28 : TwoRefParams
//	{
//		protected override int Execute(ref int x, ref int y)
//		{
//			F(ref x, out y);
//			return x + y;
//		}

//		private void F(ref int x, out int y)
//		{
//			x = x + 1;
//			y = x;
//		}
//	}

//	internal class T29 : OneValParam
//	{
//		protected override int Execute(int x)
//		{
//			int y = x;
//			int z = x + 1;
//			F(ref y, out z);
//			return z + x + y;
//		}

//		private void F(ref int x, out int y)
//		{
//			x = x + 1;
//			y = x;
//		}
//	}

//	internal class T30 : OneValParam
//	{
//		private readonly Q q = new Q();

//		protected override int Execute(int x)
//		{
//			return x + x > 0 ? q.M(ref x) + Q.S(ref x) : Q.S(ref x) - q.M(ref x);
//		}

//		private class Q
//		{
//			public int M(ref int x)
//			{
//				return x++;
//			}

//			public static int S(ref int x)
//			{
//				return x--;
//			}
//		}
//	}

//	internal class T31 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
//		{
//			if (x == y)
//				return;
//			_f1 = x;
//		}
//	}

//	internal class T32 : OneRefParam
//	{
//		protected override int Execute(ref int x)
//		{
//			return x;
//		}
//	}

//	internal class T33 : OneRefParam
//	{
//		protected override int Execute(ref int x)
//		{
//			x = 17;
//			return x;
//		}
//	}
//}