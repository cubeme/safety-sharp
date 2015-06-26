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

namespace Tests.Execution.ProvidedPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal abstract class X2 : TestComponent
	{
		protected virtual int P
		{
			get { return 17; }
		}

		protected virtual int R
		{
			get { return 21; }
		}

		protected abstract int S { get; }

		protected virtual int M(int i)
		{
			return i * 2;
		}

		protected abstract bool Q(int i);

		protected virtual int N(int i)
		{
			return i / 2;
		}
	}

	internal class X3 : X2
	{
		protected override int P
		{
			get { return 22; }
		}

		protected override int R
		{
			get { return base.R + 3; }
		}

		protected override int S
		{
			get { return 99; }
		}

		protected override int M(int i)
		{
			return i * i;
		}

		protected override bool Q(int i)
		{
			return i % 2 == 0;
		}

		protected override int N(int i)
		{
			return base.N(i) + 2;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			M(4).ShouldBe(16);
			M(10).ShouldBe(100);

			base.M(4).ShouldBe(8);
			base.M(10).ShouldBe(20);

			Q(2).ShouldBe(true);
			Q(3).ShouldBe(false);

			N(10).ShouldBe(7);
			N(100).ShouldBe(52);

			base.N(10).ShouldBe(5);
			base.N(100).ShouldBe(50);

			S.ShouldBe(99);

			base.P.ShouldBe(17);
			P.ShouldBe(22);

			base.R.ShouldBe(21);
			R.ShouldBe(24);
		}
	}
}