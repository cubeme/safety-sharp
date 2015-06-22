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

//	internal class T18 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
//		{
//			if ((x += _f1 = x) > y || --y == 0)
//				x++;
//			else if (x + (_f1++) - 2 < y + 1 || --y == 0)
//			{
//				--y;
//				if ((_f2 = ++x) == --y - --_f2)
//					--y;
//				return;
//			}
//			else
//				x -= 1;
//			_f1 = x * _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2);
//		}
//	}

//	internal class T19 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
//		{
//			if ((x += _f1 = x) > y || --y == 0)
//			{
//				x++;
//				return;
//			}
			
//			if (x + (_f1++) - 2 < y + 1 || --y == 0)
//			{
//				--y;
//				if ((_f2 = ++x) == --y - --_f2)
//					--y;
//			}
//			else
//				x -= 1;
//			_f1 = x * _f1 + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2)) + _f2);
//		}
//	}

//	internal class T20 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
//		{
//			if ((_f1 += F1(_f2--)) == 2)
//				return;
//			_f2 = F2() + F3();
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

//		private int F3()
//		{
//			return --_f2;
//		}
//	}

//	internal class T21 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
//		{
//			F3();
//			if ((x += _f1 = x) > y || --y == 0)
//			{
//				F3();
//				x++;
//				return;
//			}
			
//			if (x + (_f1++) - 2 < y + 1 || --y == 0)
//			{
//				_f1 = --y;
//				if ((_f2 = ++x) == --y - (_f2 = (--_f2 + F1(_f2))))
//					--y;
//			}
//			else
//				x -= 1;
//			_f1 = _f1 * x * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2);
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

//	internal class T22 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
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
//				{
//					_f2 = --y;
//					return;
//				}
//			}
//			else
//				x -= 1;
//			_f1 = x + _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2);
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

//	internal class T23 : TwoValParamsVoid
//	{
//		protected override void Execute(int x, int y)
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
//			{
//				F2();
//				_f2 = x -= 1;
//				return;
//			}
//			_f1 = -x + _f1 * F1(_f1 < 0 ? --_f1 : ++_f2) + (y * 2 - ((_f1 = --_f1) > 0 ? ++_f1 : (_f1 += _f2 + F1(_f2--))) + _f2);
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
//}