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

namespace Tests.Execution.SemanticEquality.SideEffectsFree
{
	using System;
	using SafetySharp.Modeling;

	internal class C18 : SemanticEqualityComponent
	{
		private readonly C _c = new C();
		private int _f;

		public int M1
		{
			[Test(1)]
			get { return 1; }
		}

		public int M2
		{
			[Test(16)]
			set { _f = value; }
		}

		public int M3
		{
			[Test(1)]
			get;
			[Test(1)]
			set;
		}

		[Test(16)]
		public int M4(int value)
		{
			M3 = value;
			return M3;
		}

		[Test(16)]
		public int M5(int value)
		{
			_c.F = value;
			return _c.F;
		}

		private class C : Component
		{
			public int F { get; set; }
		}
	}
}