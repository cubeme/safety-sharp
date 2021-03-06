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

namespace Tests.Metadata.Components.Faults
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	public class X2 : TestComponent
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults.Length.ShouldBe(2);

			Metadata.Faults[0].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Faults[0].Fault.GetType().ShouldBe(typeof(F1));
			Metadata.Faults[0].Name.ShouldBe("F1");
			Metadata.Faults[0].Fault.Component.ShouldBe(this);
			Metadata.Faults[0].OccurrencePattern.OccurrencePattern.GetType().ShouldBe(typeof(Transient));

			Metadata.Faults[1].DeclaringComponent.ShouldBe(this.GetMetadata());
			Metadata.Faults[1].Fault.GetType().ShouldBe(typeof(F2));
			Metadata.Faults[1].Name.ShouldBe("F2");
			Metadata.Faults[1].Fault.Component.ShouldBe(this);
			Metadata.Faults[1].OccurrencePattern.OccurrencePattern.GetType().ShouldBe(typeof(Persistent));
		}

		public void M()
		{
		}

		[Transient]
		private class F1 : Fault
		{
			public void M()
			{
			}
		}

		[Persistent]
		private class F2 : Fault<X2>
		{
			public void M()
			{
			}
		}
	}
}