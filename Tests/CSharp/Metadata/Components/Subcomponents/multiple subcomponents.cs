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

namespace Tests.Metadata.Components.Subcomponents
{
	using System;
	using SafetySharp.CompilerServices;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal interface I1 : IComponent
	{
	}

	internal class C2 : Component
	{
		public C2(string name)
			: base(name)
		{
		}
	}

	internal class C3 : Component, I1
	{
	}

	internal class X3 : TestComponent
	{
		private readonly C2 _c = new C2("name");
		private readonly I1 _i = new C3();

		[SuppressTransformation]
		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(2);

			Metadata.Subcomponents[0].Component.ShouldBe(_c);
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetMetadata());
			Metadata.Subcomponents[0].Name.ShouldBe("name");

			Metadata.Subcomponents[1].Component.ShouldBe((Component)_i);
			Metadata.Subcomponents[1].ParentComponent.ShouldBe(this.GetMetadata());
			Metadata.Subcomponents[1].Name.ShouldBe("_i");
		}
	}
}