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

namespace Tests.Runtime.Fields
{
	using System;
	using Shouldly;

	internal class X2 : TestComponent
	{
		private readonly int _x = 0;

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			CheckField(typeof(int), "_x", _x);
		}
	}

	internal class X3 : TestComponent
	{
		private readonly double _x = 0;

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			CheckField(typeof(double), "_x", _x);
		}
	}

	internal class X4 : TestComponent
	{
		private readonly bool _x = false;

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			CheckField(typeof(bool), "_x", _x);
		}
	}

	internal class X5 : TestComponent
	{
		private readonly E _x = E.A;

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			CheckField(typeof(E), "_x", _x);
		}

		private enum E
		{
			A
		}
	}
}