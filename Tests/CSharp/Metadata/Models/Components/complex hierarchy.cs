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

	internal class C4 : Component
	{
		private IComponent _a;
		private IComponent _b;

		public C4(IComponent a, IComponent b)
		{
			_a = a;
			_b = b;
		}
	}

	internal class C5<T> : Component
	{
		private T _c;

		public C5(T c)
		{
			_c = c;
		}
	}

	internal class C6 : Component
	{
	}

	internal class M6 : TestModel
	{
		private readonly C4 _c1;
		private readonly C6 _c2 = new C6();
		private readonly C6 _c3 = new C6();
		private readonly C6 _c4 = new C6();
		private readonly C5<C4> _c5;
		private readonly C5<C6> _c6;
		private readonly C4 _c7;
		private readonly C6 _c8 = new C6();
		private readonly C5<C6> _c9;

		public M6()
		{
			_c1 = new C4(_c2, _c3);
			_c5 = new C5<C4>(_c1);
			_c6 = new C5<C6>(_c4);
			_c7 = new C4(_c5, _c6);
			_c9 = new C5<C6>(_c8);

			AddRootComponents(_c7, _c9);
		}

		protected override void Check()
		{
			Metadata.RootComponent.Subcomponents.ShouldBe(new[] { _c7.Metadata, _c9.Metadata });
			_c7.Metadata.Subcomponents.ShouldBe(new[] { _c5.Metadata, _c6.Metadata });
			_c9.Metadata.Subcomponents.ShouldBe(new[] { _c8.Metadata });
			_c8.Metadata.Subcomponents.ShouldBeEmpty();
			_c5.Metadata.Subcomponents.ShouldBe(new[] { _c1.Metadata });
			_c6.Metadata.Subcomponents.ShouldBe(new[] { _c4.Metadata });
			_c1.Metadata.Subcomponents.ShouldBe(new[] { _c2.Metadata, _c3.Metadata });
			_c2.Metadata.Subcomponents.ShouldBeEmpty();
			_c3.Metadata.Subcomponents.ShouldBeEmpty();

			Metadata.Components.ShouldBe(new[]
			{
				Metadata.RootComponent, _c1.Metadata, _c2.Metadata, _c3.Metadata, _c4.Metadata,
				_c5.Metadata, _c6.Metadata, _c7.Metadata, _c8.Metadata, _c9.Metadata
			}, ignoreOrder: true);
		}
	}

	internal class M7 : TestObject
	{
		protected override void Check()
		{
			var c2 = new C6();
			var c3 = new C6();
			var c4 = new C6();
			var c1 = new C4(c2, c3);
			var c8 = new C6();
			var c5 = new C5<C4>(c1);
			var c6 = new C5<C6>(c4);
			var c7 = new C4(c5, c6);
			var c9 = new C5<C6>(c8);

			var m = new Model();
			m.AddRootComponents(c7, c9);
			m.Seal();

			m.Metadata.RootComponent.Subcomponents.ShouldBe(new[] { c7.Metadata, c9.Metadata });
			c7.Metadata.Subcomponents.ShouldBe(new[] { c5.Metadata, c6.Metadata });
			c9.Metadata.Subcomponents.ShouldBe(new[] { c8.Metadata });
			c8.Metadata.Subcomponents.ShouldBeEmpty();
			c5.Metadata.Subcomponents.ShouldBe(new[] { c1.Metadata });
			c6.Metadata.Subcomponents.ShouldBe(new[] { c4.Metadata });
			c1.Metadata.Subcomponents.ShouldBe(new[] { c2.Metadata, c3.Metadata });
			c2.Metadata.Subcomponents.ShouldBeEmpty();
			c3.Metadata.Subcomponents.ShouldBeEmpty();

			m.Metadata.Components.ShouldBe(new[]
			{
				m.Metadata.RootComponent, c1.Metadata, c2.Metadata, c3.Metadata, c4.Metadata,
				c5.Metadata, c6.Metadata, c7.Metadata, c8.Metadata, c9.Metadata
			}, ignoreOrder: true);
		}
	}
}