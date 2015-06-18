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

namespace Tests.Metadata.Models.Components
{
	using System;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class C1 : Component
	{
	}

	internal class M2 : TestModel
	{
		private readonly C1 _c = new C1();

		public M2()
		{
			AddRootComponent(_c);
		}

		protected override void Check()
		{
			Metadata.RootComponent.Subcomponents.ShouldBe(new[] { _c.Metadata });
			Metadata.RootComponent.Name.ShouldBe("R");
			Metadata.RootComponent.Subcomponents[0].Name.ShouldBe("_c");
			Metadata.Components.ShouldBe(new[] { Metadata.RootComponent, _c.Metadata });
		}
	}

	internal class M3 : TestObject
	{
		protected override void Check()
		{
			var c = new C1();
			var m = new Model();
			m.AddRootComponent(c);
			m.Seal();

			m.Metadata.RootComponent.Subcomponents.ShouldBe(new[] { c.Metadata });
			m.Metadata.Components.ShouldBe(new[] { m.Metadata.RootComponent, c.Metadata });
			m.Metadata.RootComponent.Subcomponents[0].Name.ShouldBe("c");

			m.Seal(); // Second call should have no effect

			m.Metadata.RootComponent.Subcomponents.ShouldBe(new[] { c.Metadata });
			m.Metadata.Components.ShouldBe(new[] { m.Metadata.RootComponent, c.Metadata });
		}
	}
}
