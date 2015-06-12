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
	using SafetySharp.CompilerServices;
	using Shouldly;

	internal class X8 : TestComponent
	{
		private readonly E _w = E.A;
		private readonly int _x = 1;
		private readonly double _y = 2;
		private readonly bool _z = false;

		public X8()
		{
			var fx = ReflectionHelpers.GetField(typeof(X8), typeof(int), "_x");
			var fy = ReflectionHelpers.GetField(typeof(X8), typeof(double), "_y");
			var fz = ReflectionHelpers.GetField(typeof(X8), typeof(bool), "_z");
			var fw = ReflectionHelpers.GetField(typeof(X8), typeof(E), "_w");

			GetBuilder().WithField(fx);
			GetBuilder().WithField(fy);
			GetBuilder().WithField(fz);
			GetBuilder().WithField(fw);

			GetBuilder().WithInitialValues(fx, _x, -1, 0);
			GetBuilder().WithInitialValues(fy, _y, -1.0, 0.0);
			GetBuilder().WithInitialValues(fz, true, _z);
			GetBuilder().WithInitialValues(fw, _w, E.B, E.D);
		}

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(4);
			CheckField(typeof(int), "_x", 1, -1, 0);
			CheckField(typeof(double), "_y", 2.0, -1.0, 0.0);
			CheckField(typeof(bool), "_z", true, false);
			CheckField(typeof(E), "_w", E.A, E.B, E.D);
		}

		private enum E
		{
			A,
			B,
			C,
			D
		}
	}
}