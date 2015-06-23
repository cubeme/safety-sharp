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

using System;

namespace Tests.Metadata.Faults.Fields
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling.Faults;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X9 : TestComponent
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Faults[0].Fields.Length.ShouldBe(4);

			Metadata.Faults[0].Fields[0].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[0].FieldInfo.ShouldBe(typeof(F).GetField("_w", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[0].InitialValues.ShouldBe(new object[] { E.A });

			Metadata.Faults[0].Fields[1].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[1].FieldInfo.ShouldBe(typeof(F).GetField("_x", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[1].InitialValues.ShouldBe(new object[] { 0 });

			Metadata.Faults[0].Fields[2].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[2].FieldInfo.ShouldBe(typeof(F).GetField("_y", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[2].InitialValues.ShouldBe(new object[] { 0.0 });

			Metadata.Faults[0].Fields[3].DeclaringObject.ShouldBe(Metadata.Faults[0].Fault.GetMetadata());
			Metadata.Faults[0].Fields[3].FieldInfo.ShouldBe(typeof(F).GetField("_z", BindingFlags.Instance | BindingFlags.NonPublic));
			Metadata.Faults[0].Fields[3].InitialValues.ShouldBe(new object[] { false });
		}

		[Transient]
		private class F : Fault
		{
			private readonly E _w = E.A;
			private readonly int _x = 0;
			private readonly double _y = 0;
			private readonly bool _z = false;
		}

		private enum E
		{
			A
		}
	}
}