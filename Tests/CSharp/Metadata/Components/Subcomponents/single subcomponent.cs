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

namespace Tests.Metadata.Components.Subcomponents
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal interface I2 : IComponent
	{
	}

	internal class C1 : Component, I2
	{
	}

	internal class X2 : TestComponent
	{
		private readonly C1 _c = new C1();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(1);

			Metadata.Subcomponents[0].Component.ShouldBe(_c);
			Metadata.Subcomponents[0].Name.ShouldBe("_c");
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetMetadata());
		}
	}

	internal class X8 : TestComponent
	{
		private readonly IComponent _c = new C1();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(1);

			Metadata.Subcomponents[0].Component.ShouldBe(_c);
			Metadata.Subcomponents[0].Name.ShouldBe("_c");
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetMetadata());
		}
	}

	internal class X9 : TestComponent
	{
		private readonly I2 _c = new C1();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(1);

			Metadata.Subcomponents[0].Component.ShouldBe((Component)_c);
			Metadata.Subcomponents[0].Name.ShouldBe("_c");
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetMetadata());
		}
	}
}