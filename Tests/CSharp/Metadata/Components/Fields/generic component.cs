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

namespace Tests.Metadata.Components.Fields
{
	using System;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X14<T1, T2> : TestComponent
	{
		public T1 _x;
		public T2 _y;

		protected X14(T1 v1, T2 v2)
		{
			_x = v1;
			_y = v2;
		}
	}

	internal class X15 : X14<int, bool>
	{
		public X15()
			: base(1, true)
		{
		}

		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(2);

			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].Field.ShouldBe(typeof(X14<int, bool>).GetField("_x"));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { _x });

			Metadata.Fields[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[1].Field.ShouldBe(typeof(X14<int, bool>).GetField("_y"));
			Metadata.Fields[1].InitialValues.ShouldBe(new object[] { _y });
		}

		internal class X16 : X14<double, X16.E>
		{
			public enum E
			{
				A,
				B,
				C
			}

			public X16()
				: base(4.2, E.B)
			{
			}

			protected override void Check()
			{
				Metadata.Fields.Length.ShouldBe(2);

				Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
				Metadata.Fields[0].Field.ShouldBe(typeof(X14<double, E>).GetField("_x"));
				Metadata.Fields[0].InitialValues.ShouldBe(new object[] { _x });

				Metadata.Fields[1].DeclaringObject.ShouldBe(this.GetMetadata());
				Metadata.Fields[1].Field.ShouldBe(typeof(X14<double, E>).GetField("_y"));
				Metadata.Fields[1].InitialValues.ShouldBe(new object[] { _y });
			}
		}
	}
}