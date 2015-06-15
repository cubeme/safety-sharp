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

namespace Tests.Metadata.Steps
{
	using System;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal abstract class X3 : TestComponent
	{
	}

	internal class X4 : X3
	{
		public override void Update()
		{
		}

		protected override void Check()
		{
			Metadata.Behaviors.Length.ShouldBe(2);

			Metadata.Behaviors[0].Method.ShouldBe(typeof(Component).GetMethod("Update"));
			Metadata.Behaviors[0].Component.Component.ShouldBe(this);
			Metadata.Behaviors[0].BaseMethod.ShouldBe(null);
			Metadata.Behaviors[0].IsOverride.ShouldBe(false);
			Metadata.Behaviors[0].Name.ShouldBe("Update");

			Metadata.Behaviors[1].Method.ShouldBe(typeof(X4).GetMethod("Update"));
			Metadata.Behaviors[1].Component.Component.ShouldBe(this);
			Metadata.Behaviors[1].BaseMethod.ShouldBe(ComponentUpdatedMethod);
			Metadata.Behaviors[1].IsOverride.ShouldBe(true);
			Metadata.Behaviors[1].Name.ShouldBe("Update");
		}
	}
}