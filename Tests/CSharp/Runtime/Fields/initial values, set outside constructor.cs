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

namespace Tests.Runtime.Fields
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;

	internal class X6 : TestComponent
	{
		private readonly E _w = E.B;
		private readonly int _x = 3;
		private readonly double _y = 5.5;
		private readonly bool _z = true;

		public X6()
		{
			GetBuilder().WithField(ReflectionHelpers.GetField(typeof(X6), typeof(int), "_x"));
			GetBuilder().WithField(ReflectionHelpers.GetField(typeof(X6), typeof(double), "_y"));
			GetBuilder().WithField(ReflectionHelpers.GetField(typeof(X6), typeof(bool), "_z"));
			GetBuilder().WithField(ReflectionHelpers.GetField(typeof(X6), typeof(E), "_w"));
		}

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(4);
			CheckField(typeof(int), "_x", _x);
			CheckField(typeof(double), "_y", _y);
			CheckField(typeof(bool), "_z", _z);
			CheckField(typeof(E), "_w", _w);
		}

		private enum E
		{
			A,
			B
		}
	}
}