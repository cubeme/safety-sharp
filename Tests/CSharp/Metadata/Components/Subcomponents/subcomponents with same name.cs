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
	using System.Reflection;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class X10 : Component
	{
	}

	internal abstract class X11 : TestComponent
	{
		private readonly X10 _c = new X10();
		public readonly X10 D = new X10();
	}

	internal abstract class X12 : X11
	{
		public new readonly X10 D = new X10();
	}

	internal class X13 : X12
	{
		private readonly X10 _c = new X10();
		public readonly X10 D2 = new X10();
		public new readonly X10 D = new X10();

		protected override void Check()
		{
			Metadata.Subcomponents.Length.ShouldBe(6);
			
			Metadata.Subcomponents[0].Component.ShouldBe(typeof(X11).GetField("_c", BindingFlags.NonPublic | BindingFlags.Instance).GetValue(this));
			Metadata.Subcomponents[0].Name.ShouldBe("_c");
			Metadata.Subcomponents[0].ParentComponent.ShouldBe(this.GetMetadata());

			Metadata.Subcomponents[1].Component.ShouldBe(typeof(X11).GetField("D").GetValue(this));
			Metadata.Subcomponents[1].Name.ShouldBe("D");
			Metadata.Subcomponents[1].ParentComponent.ShouldBe(this.GetMetadata());

			Metadata.Subcomponents[2].Component.ShouldBe(base.D);
			Metadata.Subcomponents[2].Name.ShouldBe("D1");
			Metadata.Subcomponents[2].ParentComponent.ShouldBe(this.GetMetadata());

			Metadata.Subcomponents[3].Component.ShouldBe(_c);
			Metadata.Subcomponents[3].Name.ShouldBe("_c1");
			Metadata.Subcomponents[3].ParentComponent.ShouldBe(this.GetMetadata());

			Metadata.Subcomponents[4].Component.ShouldBe(D2);
			Metadata.Subcomponents[4].Name.ShouldBe("D2");
			Metadata.Subcomponents[4].ParentComponent.ShouldBe(this.GetMetadata());

			Metadata.Subcomponents[5].Component.ShouldBe(D);
			Metadata.Subcomponents[5].Name.ShouldBe("D3");
			Metadata.Subcomponents[5].ParentComponent.ShouldBe(this.GetMetadata());
		}
	}
}