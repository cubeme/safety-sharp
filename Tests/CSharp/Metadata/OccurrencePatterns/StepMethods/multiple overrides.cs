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

namespace Tests.Metadata.OccurrencePatterns.StepMethods
{
	using System;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;

	internal class X3 : TestComponent
	{
		protected override void Check()
		{
			Metadata.Faults[0].OccurrencePattern.StepMethods.Length.ShouldBe(2);

			Metadata.Faults[0].OccurrencePattern.StepMethods[0].Method.ShouldBe(typeof(P1).GetMethod("UpdateOccurrenceState"));
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].DeclaringObject.ShouldBe((object)Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].BaseMethod.ShouldBe(null);
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].IsOverride.ShouldBe(false);
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].Name.ShouldBe("UpdateOccurrenceState");
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].OccurrencePattern.StepMethods[0].Implementation.ShouldBe(typeof(P1).GetMethod("UpdateOccurrenceState"));

			Metadata.Faults[0].OccurrencePattern.StepMethods[1].Method.ShouldBe(typeof(P2).GetMethod("UpdateOccurrenceState"));
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].DeclaringObject.ShouldBe((object)Metadata.Faults[0].OccurrencePattern);
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].BaseMethod.ShouldBe(typeof(P1).GetMethod("UpdateOccurrenceState"));
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].IsOverride.ShouldBe(true);
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].Name.ShouldBe("UpdateOccurrenceState");
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].CanBeAffectedByFaultEffects.ShouldBe(false);
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].HasImplementation.ShouldBe(true);
			Metadata.Faults[0].OccurrencePattern.StepMethods[1].Implementation.ShouldBe(typeof(P2).GetMethod("UpdateOccurrenceState"));
		}

		private class P1 : OccurrencePattern
		{
			public override void UpdateOccurrenceState()
			{
			}
		}

		private class P2 : P1
		{
			public override void UpdateOccurrenceState()
			{
			}
		}

		[OccurrencePattern(typeof(P2))]
		private class F : Fault
		{
		}
	}
}