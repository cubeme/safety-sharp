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
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime.Expressions;
	using SafetySharp.Runtime.Statements;

	internal class C4 : SemanticEqualityComponent
	{
		private readonly C _c = new C();
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

		[Test(1)]
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