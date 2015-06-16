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
	using System.Reflection;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class X7 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(4);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P).GetField("_w", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { E.B });

			Metadata.Faults[0].OccurrencePattern.Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[1].Field.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[1].InitialValues.ShouldBe(new object[] { 17 });

			Metadata.Faults[0].OccurrencePattern.Fields[2].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[2].Field.ShouldBe(typeof(P).GetField("_y", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[2].InitialValues.ShouldBe(new object[] { 3.14 });

			Metadata.Faults[0].OccurrencePattern.Fields[3].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[3].Field.ShouldBe(typeof(P).GetField("_z", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[3].InitialValues.ShouldBe(new object[] { true });
		}

		private class P : OccurrencePattern
		{
			private readonly E _w;
			private readonly int _x;
			private readonly double _y;
			private readonly bool _z;

			public P()
			{
				_x = 17;
				_y = 3.14;
				_z = true;
				_w = E.B;
			}

			public override void UpdateOccurrenceState()
			{
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
		}

		private enum E
		{
			A,
			B
		}
	}
}