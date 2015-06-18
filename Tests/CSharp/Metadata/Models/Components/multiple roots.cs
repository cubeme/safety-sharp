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

	internal class C2 : Component
	{
	}

	internal class C3 : Component
	{
		public C3(string name = null)
			: base(name)
		{
		}
	}

	internal class M4 : TestModel
	{
		private readonly C2 _c1 = new C2();
		private readonly C3 _c2 = new C3();
		private readonly C3 _c3 = new C3("name");

		public M4()
		{
			Prop1 = new C3();

			AddRootComponent(Prop2);
			AddRootComponents(_c2, _c3);
			AddRootComponents(Prop1);
			AddRootComponents(); // should have no effect
		}

		private C3 Prop1 { get; set; }

		private C2 Prop2
		{
			get { return _c1; }
		}

		protected override void Check()
		{
			Metadata.RootComponent.Subcomponents.ShouldBe(new[] { _c1.Metadata, _c2.Metadata, _c3.Metadata, Prop1.Metadata });
			Metadata.Components.ShouldBe(new[] { Metadata.RootComponent, _c1.Metadata, _c2.Metadata, _c3.Metadata, Prop1.Metadata });

			Metadata.RootComponent.Subcomponents[0].Name.ShouldBe("C2");
			Metadata.RootComponent.Subcomponents[1].Name.ShouldBe("_c2");
			Metadata.RootComponent.Subcomponents[2].Name.ShouldBe("name");
			Metadata.RootComponent.Subcomponents[3].Name.ShouldBe("Prop1");
		}
	}

	internal class M5 : TestObject
	{
		protected override void Check()
		{
			var c1 = new C2();
			var c2 = new C2();
			var c3 = new C3("name");
			var c4 = new C2();

			var m = new Model();
			m.AddRootComponent(c1);
			m.AddRootComponents(c2, c3);
			m.AddRootComponents(c4);
			m.AddRootComponents(); // should have no effect
			m.Seal();

			m.Metadata.RootComponent.Subcomponents.ShouldBe(new[] { c1.Metadata, c2.Metadata, c3.Metadata, c4.Metadata });
			m.Metadata.Components.ShouldBe(new[] { m.Metadata.RootComponent, c1.Metadata, c2.Metadata, c3.Metadata, c4.Metadata });

			m.Metadata.RootComponent.Subcomponents[0].Name.ShouldBe("c1");
			m.Metadata.RootComponent.Subcomponents[1].Name.ShouldBe("c2");
			m.Metadata.RootComponent.Subcomponents[2].Name.ShouldBe("name");
			m.Metadata.RootComponent.Subcomponents[3].Name.ShouldBe("c4");
		}
	}
}