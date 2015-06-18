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

namespace Tests.Metadata.Components.RequiredPorts
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X3 : TestComponent
	{
		[Required]
		internal extern void M();

		protected extern int M(int i);
		public extern bool M(ref int i);

		protected override void Check()
		{
			Metadata.RequiredPorts.Length.ShouldBe(3);

			Metadata.RequiredPorts[0].MethodInfo.ReturnType.ShouldBe(typeof(void));
			Metadata.RequiredPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[0].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[0].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[0].Name.ShouldBe("M");

			Metadata.RequiredPorts[1].MethodInfo.ReturnType.ShouldBe(typeof(int));
			Metadata.RequiredPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[1].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[1].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[1].Name.ShouldBe("M1");

			Metadata.RequiredPorts[2].MethodInfo.ReturnType.ShouldBe(typeof(bool));
			Metadata.RequiredPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.RequiredPorts[2].BaseMethod.ShouldBe(null);
			Metadata.RequiredPorts[2].IsOverride.ShouldBe(false);
			Metadata.RequiredPorts[2].Name.ShouldBe("M2");
		}
	}
}