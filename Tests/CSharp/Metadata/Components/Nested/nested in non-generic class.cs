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

namespace Tests.Metadata.Components.Nested
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X1
	{
		public abstract class Y1 : TestComponent
		{
			public int _x = 0;
		}

		public abstract class Y2<T> : TestComponent
		{
			public T _x = default(T);
		}
	}

	internal class X2 : X1.Y1
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			
			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].FieldInfo.ShouldBe(typeof(X1.Y1).GetField("_x"));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { _x });
		}
	}

	internal class X3 : X1.Y2<bool>
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(1);
			
			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].FieldInfo.ShouldBe(typeof(X1.Y2<bool>).GetField("_x"));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { _x });
		}
	}
}