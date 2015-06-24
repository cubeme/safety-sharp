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

	internal class C4 : SemanticEqualityComponent
	{
		private readonly C _c = new C();
		private int _a;
		private int _b;
		private bool _d;
		private int _f;

		public C4()
		{
			Bind(RequiredPorts.Req = ProvidedPorts.F);
		}

		private int F(int a)
		{
			return a;
		}

		private void G(ref int a)
		{
			a = a + 1;
		}

		private void H(out int a)
		{
			a = 7;
		}

		private void I(int a = 3, int b = 5, bool c = false)
		{
			_a = a;
			_b = b;
			_d = c;
		}

		private extern int Req(int a);

		[Test(4)]
		public void M1(ref int a)
		{
			a = F(a);
		}

		[Test(1)]
		public void M2(out int a)
		{
			a = this.F(2);
		}

		[Test(4)]
		public void M3(ref int a)
		{
			G(ref a);
		}

		[Test(1)]
		public void M4(out int a)
		{
			a = 3;
			G(ref a);
		}

		[Test(4)]
		public void M5(ref int a)
		{
			H(out a);
		}

		[Test(1)]
		public void M6(out int a)
		{
			H(out a);
		}

		[Test(4)]
		public void M7(ref int a)
		{
			a = Req(a);
		}

		[Test(8)]
		public void M8(out int a)
		{
			a = this.Req(2);
		}

		[Test(1)]
		public override void Update()
		{
			_c.F = 33;
			_c.Update();
			_f = _c.F + 2;
		}

		[Test(16)]
		public void M9(int a, int b, bool c)
		{
			I(a, b, c);
		}

		[Test(16)]
		public void M10(int a, int b, bool c)
		{
			I(c: c, a: b, b: a);
		}

		[Test(16)]
		public void M11(int a, int b, bool c)
		{
			I(b: b, a: a, c: c);
		}

		[Test(1)]
		public void M12()
		{
			I();
		}

		[Test(16)]
		public void M13(int b)
		{
			I(a: b);
		}

		[Test(16)]
		public void M14(int a)
		{
			I(a: a);
		}

		[Test(16)]
		public void M15(int a)
		{
			I(b: a);
		}

		[Test(16)]
		public void M16(bool c)
		{
			I(c: c);
		}

		[Test(16)]
		public void M17(int a, int b)
		{
			I(a: b, b: a);
		}

		[Test(16)]
		public void M18(int a, int b)
		{
			I(b: b, a: a);
		}

		[Test(16)]
		public void M19(int a, bool c)
		{
			I(c: c, a: a);
		}

		[Test(16)]
		public void M20(int b, bool c)
		{
			I(b: b, c: c);
		}

		[Test(16)]
		public void M21(int b, bool c)
		{
			I(c: c, b: b);
		}

		[Test(16)]
		public void M22(int a, bool c)
		{
			I(a: a, c: c);
		}

		private class C : Component
		{
			public int F;

			public override void Update()
			{
				F = F + 1;
			}
		}
	}
}