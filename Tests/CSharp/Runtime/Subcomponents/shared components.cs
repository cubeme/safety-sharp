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

namespace Tests.Runtime.Subcomponents
{
	using System;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;

	/* ===================================================================== */
	/* This should obviously be invalid; but this is check at a later stage, */
	/* so the metadata must be initialized correctly.						 */
	/* ===================================================================== */

	internal class C7 : Component
	{
	}

	internal class X7 : TestComponent
	{
		public C7 _a;
		public C7 _b;

		public X7()
		{
			_a = new C7();
			_b = _a;
		}

		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(2);

			Metadata.Subcomponents[0].Component.ShouldBe(_a);
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetComponentInfo());

			Metadata.Subcomponents[1].Component.ShouldBe(_b);
			Metadata.Subcomponents[1].ParentComponent.ShouldBe(this.GetComponentInfo());
		}
	}
}