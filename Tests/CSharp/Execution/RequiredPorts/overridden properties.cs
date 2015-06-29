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
	using Shouldly;
	using Utilities;

	internal abstract class X2b : TestComponent
	{
		protected X2b()
		{
			Bind(RequiredPorts.A = ProvidedPorts.M);
		}

		protected virtual int M
		{
			get { return 17; }
		}

		protected abstract bool Q { get; }

		protected virtual int N
		{
			get { return 33; }
		}

		protected extern int A { get; }
	}

	internal class X3b : X2b
	{
		public X3b()
		{
			Bind(RequiredPorts.B = base.ProvidedPorts.M);
			Bind(RequiredPorts.C = ProvidedPorts.Q);
			Bind(RequiredPorts.D = ProvidedPorts.N);
			Bind(RequiredPorts.E = base.ProvidedPorts.N);
		}

		protected override int M
		{
			get { return 99; }
		}

		protected override bool Q
		{
			get { return true; }
		}

		protected override int N
		{
			get { return base.N + 2; }
		}

		private extern int B { get; }
		private extern bool C{get;}
		private extern int  D{get;}
		private extern int  E{get;}

		[SuppressTransformation]
		protected override void Check()
		{
			A.ShouldBe(99);
			B.ShouldBe(17);
			C.ShouldBe(true);
			D.ShouldBe(35);
			E.ShouldBe(33);
		}
	}
}