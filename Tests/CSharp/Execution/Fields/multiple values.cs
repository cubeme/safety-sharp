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

namespace Tests.Execution.Fields
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal class C4 : TestComponent
	{
		private readonly int _f1;
		private readonly bool _f2;
		private readonly double _f3;
		private readonly E _f4;

		public C4()
		{
			SetInitialValues(_f1, 1, 4, 2);
			SetInitialValues(_f2, true, false);
			SetInitialValues(_f3, 2.5, -2.5);
			SetInitialValues(_f4, E.B, E.C);
		}

		[SuppressTransformation]
		protected override void Check()
		{
			(_f1 == 1 || _f1 == 4 || _f1 == 2).ShouldBe(true);
			(_f2 || !_f2).ShouldBe(true);
			(_f3 == 2.5 || _f3 == -2.5).ShouldBe(true);
			(_f4 == E.B || _f4 == E.C).ShouldBe(true);
		}

		private enum E
		{
			A,
			B,
			C
		}
	}
}