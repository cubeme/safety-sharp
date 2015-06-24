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

namespace Tests.Metadata.Components.Fields
{
	using System;
	using System.Reflection;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X16 : TestComponent
	{
		public int X;
	}

	internal class X17 : X16
	{
		public int X1;
		public new int X;

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Fields.Length.ShouldBe(3);

			Metadata.Fields[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[0].FieldInfo.ShouldBe(typeof(X16).GetField("X"));
			Metadata.Fields[0].Name.ShouldBe("X");
			Metadata.Fields[0].InitialValues.ShouldBe(new object[] { 0 });

			Metadata.Fields[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[1].FieldInfo.ShouldBe(typeof(X17).GetField("X1"));
			Metadata.Fields[1].Name.ShouldBe("X1");
			Metadata.Fields[1].InitialValues.ShouldBe(new object[] { 0 });

			Metadata.Fields[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.Fields[2].FieldInfo.ShouldBe(typeof(X17).GetField("X"));
			Metadata.Fields[2].Name.ShouldBe("X2");
			Metadata.Fields[2].InitialValues.ShouldBe(new object[] { 0 });
		}
	}
}