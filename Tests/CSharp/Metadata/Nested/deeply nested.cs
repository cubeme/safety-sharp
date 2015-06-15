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

namespace Tests.Metadata.Nested
{
	using System;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X7<T>
	{
		public class A
		{
			public class B<U>
			{
				public class C
				{
					public abstract class Y<S> : TestComponent
					{
						public T _x = default(T);
						public S _y = default(S);
						public U _z = default(U);
					}
				}
			}
		}
	}

	internal class X8 : X7<double>.A.B<int>.C.Y<bool>
	{
		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(3);

			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].Field.ShouldBe(typeof(X7<double>.A.B<int>.C.Y<bool>).GetField("_x"));
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { _x });

			Metadata.Fields[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[1].Field.ShouldBe(typeof(X7<double>.A.B<int>.C.Y<bool>).GetField("_y"));
			Metadata.Fields[1].InitialValues.ShouldBe(new object[] { _y });

			Metadata.Fields[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[2].Field.ShouldBe(typeof(X7<double>.A.B<int>.C.Y<bool>).GetField("_z"));
			Metadata.Fields[2].InitialValues.ShouldBe(new object[] { _z });
		}
	}
}