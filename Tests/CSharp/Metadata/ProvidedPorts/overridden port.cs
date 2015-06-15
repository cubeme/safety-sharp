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

namespace Tests.Metadata.ProvidedPorts
{
	using System;
	using SafetySharp.CompilerServices;
	using Shouldly;
	using Utilities;

	internal abstract class X8 : TestComponent
	{
		public virtual bool M(ref int i)
		{
			return i == 2;
		}

		public abstract bool N(out bool i);
	}

	internal class X9 : X8
	{
		public override bool M(ref int i)
		{
			return false;
		}

		public override bool N(out bool i)
		{
			i = false;
			return true;
		}

		[Ignore]
		protected override void Check()
		{
			Metadata.ProvidedPorts.Length.ShouldBe(3);

			Metadata.ProvidedPorts[0].Method.ShouldBe(typeof(X8).GetMethod("M"));
			Metadata.ProvidedPorts[0].Component.Component.ShouldBe(this);
			Metadata.ProvidedPorts[0].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[0].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[0].Name.ShouldBe("M");

			Metadata.ProvidedPorts[1].Method.ShouldBe(typeof(X9).GetMethod("M"));
			Metadata.ProvidedPorts[1].Component.Component.ShouldBe(this);
			Metadata.ProvidedPorts[1].BaseMethod.ShouldBe(typeof(X8).GetMethod("M"));
			Metadata.ProvidedPorts[1].IsOverride.ShouldBe(true);
			Metadata.ProvidedPorts[1].Name.ShouldBe("M");

			Metadata.ProvidedPorts[2].Method.ShouldBe(typeof(X9).GetMethod("N"));
			Metadata.ProvidedPorts[2].Component.Component.ShouldBe(this);
			Metadata.ProvidedPorts[2].BaseMethod.ShouldBe(null);
			Metadata.ProvidedPorts[2].IsOverride.ShouldBe(false);
			Metadata.ProvidedPorts[2].Name.ShouldBe("N");
		}
	}
}