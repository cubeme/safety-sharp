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

namespace Tests.Metadata.Components.Fields
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X10 : TestComponent
	{
		public int _x = 11;
	}

	internal class X11 : X10
	{
		private new readonly int _x = 17;

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(2);

			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].FieldInfo.ShouldBe(typeof(X10).GetField("_x"));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { ((X10)this)._x });

			Metadata.Fields[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[1].FieldInfo.ShouldBe(typeof(X11).GetField("_x", BindingFlags.Instance| BindingFlags.NonPublic));
			Metadata.Fields[1].InitialValues.ShouldBe(new object[] { _x });
		}
	}
}