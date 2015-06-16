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

namespace Tests.Metadata.OccurrencePatterns.Fields
{
	using System;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class P<T1, T2> : OccurrencePattern
	{
		public T1 _x;
		public T2 _y;

		public override bool UpdateOccurrenceState()
		{
			return true;
		}
	}

	internal class X15 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(2);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P<int, bool>).GetField("_x"));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { 0 });

			Metadata.Faults[0].OccurrencePattern.Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[1].Field.ShouldBe(typeof(P<int, bool>).GetField("_y"));
			Metadata.Faults[0].OccurrencePattern.Fields[1].InitialValues.ShouldBe(new object[] { false });

			Metadata.Faults[1].OccurrencePattern.Fields.Length.ShouldBe(2);

			Metadata.Faults[1].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[1].OccurrencePattern);
			Metadata.Faults[1].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P<double, E>).GetField("_x"));
			Metadata.Faults[1].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { 0.0 });

			Metadata.Faults[1].OccurrencePattern.Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[1].OccurrencePattern);
			Metadata.Faults[1].OccurrencePattern.Fields[1].Field.ShouldBe(typeof(P<double, E>).GetField("_y"));
			Metadata.Faults[1].OccurrencePattern.Fields[1].InitialValues.ShouldBe(new object[] { E.A });
		}

		private enum E
		{
			A,
			B,
			C
		}

		[OccurrencePattern(typeof(P<int, bool>))]
		public class F1 : Fault
		{
		}

		[OccurrencePattern(typeof(P<double, E>))]
		public class F2 : Fault
		{
		}
	}
}