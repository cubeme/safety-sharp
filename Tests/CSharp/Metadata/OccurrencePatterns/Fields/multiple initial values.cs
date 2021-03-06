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

namespace Tests.Metadata.OccurrencePatterns.Fields
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class X8 : TestComponent
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.Fields.Length.ShouldBe(4);

			Metadata.Faults[0].OccurrencePattern.Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[0].FieldInfo.ShouldBe(typeof(P).GetField("_w", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[0].InitialValues.ShouldBe(new object[] { E.A, E.B, E.D });

			Metadata.Faults[0].OccurrencePattern.Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[1].FieldInfo.ShouldBe(typeof(P).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[1].InitialValues.ShouldBe(new object[] { 1, -1, 0 });

			Metadata.Faults[0].OccurrencePattern.Fields[2].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[2].FieldInfo.ShouldBe(typeof(P).GetField("_y", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[2].InitialValues.ShouldBe(new object[] { 2.0, -1.0, 0.0 });

			Metadata.Faults[0].OccurrencePattern.Fields[3].DeclaringObject.ShouldBe(Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.Fields[3].FieldInfo.ShouldBe(typeof(P).GetField("_z", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].OccurrencePattern.Fields[3].InitialValues.ShouldBe(new object[] { true, false });
		}

		private class P : OccurrencePattern
		{
			private readonly E _w = E.A;
			private readonly int _x = 1;
			private readonly double _y = 2;
			private readonly bool _z = false;

			public P()
			{
				SetInitialValues(_x, _x, -1, 0);
				SetInitialValues(_y, _y, -1.0, 0.0);
				SetInitialValues(_z, true, _z);
				SetInitialValues(_w, _w, E.B, E.D);
			}

			public override bool UpdateOccurrenceState()
			{
				return true;
			}
		}

		[OccurrencePattern(typeof(P))]
		private class F : Fault
		{
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