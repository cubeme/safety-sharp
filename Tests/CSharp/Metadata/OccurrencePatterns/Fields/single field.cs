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

	internal class X2 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(1);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { 0 });
		}

		private class P : OccurrencePattern
		{
			private readonly int _x = 0;

			public override void Update()
			{
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
		}
	}

	internal class X3 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(1);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { 0.0 });
		}

		private class P : OccurrencePattern
		{
			private readonly double _x = 0;

			public override void Update()
			{
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
		}
	}

	internal class X4 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(1);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { false });
		}

		private class P : OccurrencePattern
		{
			private readonly bool _x = false;

			public override void Update()
			{
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
		}
	}

	internal class X5 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(1);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].Field.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { E.A });
		}

		private class P : OccurrencePattern
		{
			private readonly E _x = E.A;

			public override void Update()
			{
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
		}

		private enum E
		{
			A
		}
	}
}