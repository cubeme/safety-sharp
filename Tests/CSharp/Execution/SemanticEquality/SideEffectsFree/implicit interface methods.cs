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

	internal interface I1 : IComponent
	{
		[Provided]
		bool F(bool b);

		[Provided]
		int G(ref int a);

		[Provided]
		int H(int a);
	}

	internal class C14 : SemanticEqualityComponent, I1
	{
		private readonly I1 _c1 = new C1();
		private readonly I1 _c2 = new C2();

		public bool F(bool a)
		{
			return a;
		}

		public int G(ref int a)
		{
			a = a * 33;
			return a + 17;
		}

		public int H(int a)
		{
			return a * a;
		}

		[Test(4)]
		public bool M1(bool a)
		{
			return F(a);
		}

		[Test(4)]
		public bool M2(bool a)
		{
			return this.F(a);
		}

		[Test(16)]
		public int M4(ref int a)
		{
			return G(ref a);
		}

		[Test(16)]
		public int M5(ref int a)
		{
			return this.G(ref a);
		}

		[Test(16)]
		public int M6(int a)
		{
			return H(a);
		}

		[Test(16)]
		public int M7(int a)
		{
			return this.H(a);
		}

		[Test(16)]
		public int M9(ref int a)
		{
			return this._c1.G(ref a);
		}

		[Test(16)]
		public int M10(ref int a)
		{
			return this._c2.G(ref a);
		}

		[Test(16)]
		public int M11(int a)
		{
			return _c1.H(a);
		}

		[Test(16)]
		public int M12(int a)
		{
			return this._c2.H(a);
		}

		[Test(4)]
		public bool M13(bool a)
		{
			return this._c1.F(a);
		}

		[Test(4)]
		public bool M14(bool a)
		{
			return this._c2.F(a);
		}

		private class C1 : Component, I1
		{
			public bool F(bool b)
			{
				return !b;
			}

			public int G(ref int a)
			{
				return a - 3;
			}

			public virtual int H(int a)
			{
				return a + a - 3;
			}
		}

		private class C2 : C1
		{
			public override int H(int a)
			{
				return base.H(a) - 5;
			}
		}
	}
}