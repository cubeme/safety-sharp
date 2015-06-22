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

//	internal class T8 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			var r = x + y / 2;
//			if ((r *= 2) == y++ || y-- == --y)
//				r += y * x;
//			else
//				r--;
//			return r;
//		}
//	}

//	internal class T9 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			if ((x += x) > y || --y == 0)
//				x++;
//			else if (x - 2 < y + 1 || --y == 0)
//			{
//				--y;
//				if (++x == --y)
//					--y;
//			}
//			else
//				x -= 1;
//			return x *= y * 2;
//		}
//	}

//	internal class T10 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			if ((x + x) > y || y == 0)
//				x++;
//			else if (x - 2 < y + 1 || y - 1 == 0)
//			{
//				--y;
//				if (x == y)
//					--y;
//			}
//			else
//				x -= 1;
//			return x *= y * 2;
//		}
//	}

//	internal class T11 : FourValParams
//	{
//		protected override int Execute(int arg1, int arg2, bool arg3, bool arg4)
//		{
//			var loc0 = 0;
//			if (arg1 > 0)
//				loc0 += arg1;
//			var loc1 = loc0 != 0;
//			var loc2 = arg2 > 3 && arg3;
//			var loc3 = arg4 && !loc2 && loc1;
//			var loc4 = arg4 && loc2 && loc1;
//			if (loc3)
//				--loc0;
//			if (loc4)
//				--loc0;
//			return loc0;
//		}
//	}

//	internal class T12 : FourValParams
//	{
//		protected override int Execute(int arg1, int arg2, bool arg3, bool arg4)
//		{
//			var loc0 = 0;
//			if (arg1 > 0)
//				loc0 += arg1;
//			var loc1 = loc0 != 0;
//			var loc2 = arg2 != 17 & arg3;
//			var loc3 = arg4 & !loc2 & loc1;
//			var loc4 = arg4 & loc2 & loc1;
//			if (loc3)
//				--loc0;
//			if (loc4)
//				--loc0;
//			return loc0;
//		}
//	}

//	internal class T13 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			if ((x += _f1 = x) > y || --y == 0)
//				x++;
//			else if (x + (_f1++) - 2 < y + 1 || --y == 0)
//			{
//				--y;
//				if ((_f2 = ++x) == --y - --_f2)
//					--y;
//			}
//			else
//				x -= 1;
//			return x *= _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2);
//		}
//	}

//	internal class T14 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			return _f1 += F1(_f2--);
//		}

//		private int F1(int x)
//		{
//			++_f1;
//			_f2 += x;
//			return x;
//		}

//		private int F2()
//		{
//			return ++_f1;
//		}

//		private void F3()
//		{
//			--_f2;
//		}
//	}

//	internal class T15 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			F3();
//			if ((x += _f1 = x) > y || --y == 0)
//			{
//				F3();
//				x++;
//			}
//			else if (x + (_f1++) - 2 < y + 1 || --y == 0)
//			{
//				--y;
//				if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2))))
//					--y;
//			}
//			else
//				x -= 1;
//			return x *= _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2);
//		}

//		private int F1(int x)
//		{
//			++_f1;
//			_f2 += x;
//			return x;
//		}

//		private int F2()
//		{
//			return ++_f1;
//		}

//		private void F3()
//		{
//			--_f2;
//		}
//	}

//	internal class T16 : TwoValParams
//	{
//		protected override int Execute(int x, int y)
//		{
//			_f1 = x;
//			if (x > 0 || F(ref x, out y) && !F(ref _f1, out _f2))
//			{
//				F(ref y, out _f1);
//			}
//			return x + _f1 + _f2 + y + (_f1 > 0 && F(ref x, out x) ? (F(ref _f2, out y) ? 1 : 0) : F(ref x, out x) ? 0 : 1) + x + _f1 + _f2 + y;
//		}

//		private bool F(ref int x, out int y)
//		{
//			x = x + 1;
//			y = x;
//			return y > 0;
//		}
//	}

//	internal class T17 : TwoRefParams
//	{
//		protected override int Execute(ref int x, ref int y)
//		{
//			_f1 = x;
//			if (x > 0 || F(ref x, out y) && !F(ref _f1, out _f2))
//			{
//				F(ref y, out _f1);
//			}
//			return x + _f1 + _f2 + y + (_f1 > 0 && F(ref x, out x) ? (F(ref _f2, out y) ? 1 : 0) : F(ref x, out x) ? 0 : 1) + x + _f1 + _f2 + y;
//		}

//		private bool F(ref int x, out int y)
//		{
//			x = x + 1;
//			y = x;
//			return y > 0;
//		}
//	}

//	internal class T35 : OneValParam
//	{
//		protected override int Execute(int z)
//		{
//			z *= z-- * --z;
//			return z;
//		}
//	}

//	internal class T36 : OneRefParam
//	{
//		protected override int Execute(ref int z)
//		{
//			z *= z-- * --z;
//			return z;
//		}
//	}

//	internal class T37 : TwoRefParams
//	{
//		protected override int Execute(ref int y, ref int z)
//		{
//			var q = y > 0;
//			z = q ? z++ : ((q = !q) ? z-- : --z);
//			return q ? z : z + 1;
//		}
//	}

//	internal class T38 : TwoValParams
//	{
//		protected override int Execute(int b, int c)
//		{
//			var q = b <= 0;
//			var x = 1 + ((q = !q) ? (c++ > 2 ? c-- : --c) : ((q = (!q ? (q = !q) : q)) ? c += 17 : c -= 8));
//			return q ? x + 1 : x;
//		}
//	}

//	internal class T39 : TwoOtherParams
//	{
//		protected override bool Execute(ref bool q, int c)
//		{
//			var x = 1 + ((q = !q) ? (c++ > 2 ? c-- : --c) : ((q = (!q ? (q = !q) : q)) ? c += 17 : c -= 8));
//			return q ? x - 1 > c : x < c;
//		}
//	}

//	internal class T40 : OneRefParam
//	{
//		protected override int Execute(ref int b)
//		{
//			var q = b > 2;
//			return 1 + ((q = (!q ? (q = !q) : q)) ? 17 : 8);
//		}
//	}
//}