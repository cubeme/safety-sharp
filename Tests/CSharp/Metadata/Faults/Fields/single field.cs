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

namespace Tests.Metadata.Faults.Fields
{
	using System;
	using System.Reflection;
	using SafetySharp.Modeling.Faults;
	using Shouldly;
	using Utilities;
	using SafetySharp.Runtime;

	internal class X2 : TestComponent
	{
		[Transient]
		private class F : Fault
		{
			private readonly int _x = 0;
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(1);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].FieldInfo.ShouldBe(typeof(F).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { 0 });
		}
	}

	internal class X3 : TestComponent
	{
		[Transient]
		private class F : Fault
		{
			private readonly double _x = 0;
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(1);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].FieldInfo.ShouldBe(typeof(F).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { 0.0 });
		}
	}

	internal class X4 : TestComponent
	{
		[Transient]
		private class F : Fault
		{
			private readonly bool _x = false;
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(1);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].FieldInfo.ShouldBe(typeof(F).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { false });
		}
	}

	internal class X5 : TestComponent
	{
		[Transient]
		private class F : Fault
		{
			private readonly E _x = E.A;
		}

		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(1);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].FieldInfo.ShouldBe(typeof(F).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { E.A });
		}

		private enum E
		{
			A
		}
	}
}