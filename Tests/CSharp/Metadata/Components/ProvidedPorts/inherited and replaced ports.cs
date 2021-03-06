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

namespace Tests.Metadata.Components.ProvidedPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal abstract class X4 : TestComponent
	{
		public bool M(ref int i)
		{
			return i == 2;
		}
	}

	internal class X5 : X4
	{
		public void Q(out int i)
		{
			i = 2;
		}

		public new bool M(ref int i)
		{
			return i == 2;
		}

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(3);

			Metadata.ProvidedPorts[0].MethodInfo.ShouldBe(typeof(X4).GetMethod("M"));
			Metadata.ProvidedPorts[0].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");

			Metadata.ProvidedPorts[1].MethodInfo.ShouldBe(typeof(X5).GetMethod("Q"));
			Metadata.ProvidedPorts[1].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[1].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[1].Name.ShouldBe("Q");

			Metadata.ProvidedPorts[2].MethodInfo.ShouldBe(typeof(X5).GetMethod("M"));
			Metadata.ProvidedPorts[2].DeclaringObject.ShouldBe(this.GetMetadata());
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[2].ImplementedMethods.ShouldBeEmpty();
			Metadata.ProvidedPorts[2].Name.ShouldBe("M1");
		}
	}
}