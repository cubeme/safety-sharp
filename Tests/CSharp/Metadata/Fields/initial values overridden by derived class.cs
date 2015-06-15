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

namespace Tests.Metadata.Fields
{
	using System;
	using System.Reflection;
	using Shouldly;
	using Utilities;

	internal abstract class X12 : TestComponent
	{
		protected int _x;

		protected X12()
		{
			SetInitialValues(_x, 1, 2, 3);
		}
	}

	internal class X13 : X12
	{
		public X13()
		{
			SetInitialValues(_x, 88, 22);
		}

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);

			Metadata.Fields[0].Component.Component.ShouldBe(this);
			Metadata.Fields[0].Field.ShouldBe(typeof(X12).GetField("_x", BindingFlags.Instance| BindingFlags.NonPublic));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { 88, 22 });
		}
	}
}