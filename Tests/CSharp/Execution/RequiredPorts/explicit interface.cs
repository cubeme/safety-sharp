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

namespace Tests.Execution.RequiredPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal interface I1 : IComponent
	{
		[Required]
		int P { get; }

		[Provided]
		int Q { get; }

		[Required]
		int N(int i);

		[Provided]
		int M(int i);
	}

	internal class X6 : TestComponent, I1
	{
		public X6()
		{
			Bind(((I1)this).RequiredPorts.N = ((I1)this).ProvidedPorts.M);
			Bind(((I1)this).RequiredPorts.P = ((I1)this).ProvidedPorts.Q);
		}

		extern int I1.N(int i);

		int I1.M(int i)
		{
			return i * 3;
		}

		extern int I1.P { get; }

		int I1.Q
		{
			get { return 22; }
		}

		[SuppressTransformation]
		protected override void Check()
		{
			((I1)this).N(2).ShouldBe(6);
			((I1)this).N(10).ShouldBe(30);

			((I1)this).P.ShouldBe(22);
		}
	}
}