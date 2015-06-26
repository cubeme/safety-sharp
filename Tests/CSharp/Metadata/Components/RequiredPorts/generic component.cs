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

namespace Tests.Metadata.Components.RequiredPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X6<T1, T2> : TestComponent
	{
		public extern T1 M(ref T2 i);
		public extern int N(int i);
	}

	internal class X7 : X6<int, bool>
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.RequiredPorts.Length.ShouldBe(2);

			Metadata.RequiredPorts[0].MethodInfo.ShouldBe(typeof(X6<int, bool>).GetMethod("M"));
			Metadata.RequiredPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[0].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[0].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[0].Name.ShouldBe("M");

			Metadata.RequiredPorts[1].MethodInfo.ShouldBe(typeof(X6<int, bool>).GetMethod("N"));
			Metadata.RequiredPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[1].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[1].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[1].Name.ShouldBe("N");
		}
	}

	internal abstract class X6b<T1, T2> : TestComponent
	{
		public extern T1 M { get; }
		public extern int N { set; }
	}

	internal class X7b : X6b<int, bool>
	{
		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.RequiredPorts.Length.ShouldBe(2);

			Metadata.RequiredPorts[0].MethodInfo.ShouldBe(typeof(X6b<int, bool>).GetMethod("get_M"));
			Metadata.RequiredPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[0].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[0].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[0].Name.ShouldBe("get_M");

			Metadata.RequiredPorts[1].MethodInfo.ShouldBe(typeof(X6b<int, bool>).GetMethod("get_N"));
			Metadata.RequiredPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[1].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[1].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[1].Name.ShouldBe("get_N");
		}
	}
}