﻿// The MIT License (MIT)
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

namespace Tests.Execution.RequiredPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal abstract class X4 : TestComponent
	{
		public int P
		{
			get { return 21; }
		}

		public extern int Q { get; }

		public int M(int i)
		{
			return i * 2;
		}

		public extern int N(int i);
	}

	internal class X5 : X4
	{
		public X5()
		{
			Bind(RequiredPorts.N = base.ProvidedPorts.M);
			Bind(base.RequiredPorts.N = ProvidedPorts.M);

			Bind(RequiredPorts.Q = base.ProvidedPorts.P);
			Bind(base.RequiredPorts.Q = ProvidedPorts.P);
		}

		private new int P
		{
			get { return 17; }
		}

		private new extern int Q { get; }

		private new int M(int i)
		{
			return i * i;
		}

		private new extern int N(int i);

		[SuppressTransformation]
		protected override void Check()
		{
			N(3).ShouldBe(6);
			N(10).ShouldBe(20);

			base.N(3).ShouldBe(9);
			base.N(10).ShouldBe(100);

			((X4)this).N(3).ShouldBe(9);
			((X4)this).N(10).ShouldBe(100);

			Q.ShouldBe(21);
			base.Q.ShouldBe(17);
			((X4)this).Q.ShouldBe(17);
		}
	}
}