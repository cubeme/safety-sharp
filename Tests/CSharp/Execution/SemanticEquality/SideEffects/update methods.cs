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

namespace Tests.Execution.SemanticEquality.SideEffects
{
	using System;
	using SafetySharp.Modeling;

	internal abstract class C14 : SemanticEqualityComponent
	{
		public int _f = 12;

		public override void Update()
		{
			_f = 99;
		}
	}

	internal abstract class C15 : C14
	{
		public int _g = 7;

		public override void Update()
		{
			base.Update();
			_g = 1 + _f;
		}
	}

	internal class C16 : C15
	{
		private readonly C _c = new C();
		public int _h;
		private int _i;

		private int M(int i)
		{
			return i * 2;
		}

		[Test(1)]
		public override void Update()
		{
			_h = _f + _g;
			_c.Update();
			base.Update();
			_i = _g + _f + _h + M(17);
		}

		private class C : Component
		{
		}
	}
}