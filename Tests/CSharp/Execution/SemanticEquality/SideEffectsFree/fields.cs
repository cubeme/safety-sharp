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
	using SafetySharp.Modeling;

	internal abstract class C8 : SemanticEqualityComponent
	{
		protected bool _f1;
		protected int _f;
	}

	internal class C9 : C8
	{
		private readonly C _c = new C();
		private readonly D _d = new D();
		private new int _f1;
		private bool _f2;

		[Test(16)]
		public int M1(int a)
		{
			_f1 = a + 1;
			_f2 = a > 0;

			return _f2 | a < 7 ? _f1 + 17 : a - 3;
		}

		[Test(16)]
		public int M2(int a)
		{
			this._f1 = a + 1;
			this._f2 = a > 0;

			return this._f2 | a < 7 ? this._f1 + 17 : a - 3;
		}

		[Test(16)]
		public void M3(ref int a, out bool b)
		{
			_f1 = a + 1;
			_f2 = a > 0;

			a = _f1 + (_f2 ? 17 : -1);
			b = _f2;
		}

		[Test(16)]
		public double M4(double a)
		{
			_c.F = a;
			return _c.F + a;
		}

		[Test(16)]
		public double M5(double a)
		{
			this._d.C.F = a;
			return this._d.C.F + a;
		}

		[Test(16)]
		public int M6(bool a, int b)
		{
			base._f1 = a;
			_f1 = b;
			_f = b + 1;

			return _f1 + (base._f1 ? 1 : 0) - this._f;
		}

		private class C : Component
		{
			public double F;
		}

		private class D : Component
		{
			public readonly C C = new C();
		}
	}
}