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

namespace Tests.Metadata.Faults.Fields
{
	using System;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X14<T1, T2> : TestComponent
	{
		[Transient]
		public class F : Fault
		{
			public T1 _x;
			public T2 _y;
		}
	}

	internal class X15 : X14<int, bool>
	{
		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(2);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].Field.ShouldBe(typeof(F).GetField("_x"));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { 0 });

			Metadata.Faults[0].Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[1].Field.ShouldBe(typeof(F).GetField("_y"));
			Metadata.Faults[0].Fields[1].InitialValues.ShouldBe(new object[] { false });
		}
	}

	internal class X16 : X14<double, X16.E>
	{
		public enum E
		{
			A,
			B,
			C
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(2);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].Field.ShouldBe(typeof(F).GetField("_x"));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { 0.0 });

			Metadata.Faults[0].Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[1].Field.ShouldBe(typeof(F).GetField("_y"));
			Metadata.Faults[0].Fields[1].InitialValues.ShouldBe(new object[] { E.A });
		}
	}
}