// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace Tests.CSharp.Transformation
{
	using System;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;

	[TestFixture]
	public class MetamodelTransformationTests
	{
		private static Model Transform(string csharpCode)
		{
			var compilation = new TestCompilation("using SafetySharp.Modeling; " + csharpCode);
			var transformation = new MetamodelTransformation();
			return transformation.Transform(compilation.Compilation);
		}

		private static ComponentDeclaration TransformComponent(string csharpCode)
		{
			return Transform(csharpCode).Components[0];
		}

		[Test]
		public void ShouldTransformOneComponentWithoutAnyMembers()
		{
			var model = Transform("class MyComponent : Component {}");
			model.Components.Length.Should().Be(1);

			var component = model.Components[0];
			component.Methods.Length.Should().Be(0);
			component.Fields.Length.Should().Be(0);
		}

		[Test]
		public void ShouldTransformSimpleComponentName()
		{
			var component = TransformComponent("class MyComponent : Component {}");
			component.Identifier.Name.Should().Be("MyComponent");
		}

		[Test]
		public void ShouldTransformNamespacedComponentName()
		{
			var component = TransformComponent("namespace Tests.Components { class MyComponent : Component {} }");
			component.Identifier.Name.Should().Be("Tests.Components.MyComponent");
		}

		[Test]
		public void ShouldTransformSingleField()
		{
			var component = TransformComponent("class X : Component { private bool value; }");
			component.Fields.Length.Should().Be(1);

			var field = component.Fields[0];
			field.Identifier.Name.Should().Be("value");
		}

		[Test]
		public void ShouldTransformMultipleFields()
		{
			var component = TransformComponent("class X : Component { private bool value; private bool test; private bool other; }");
			component.Fields.Length.Should().Be(3);

			var field1 = component.Fields[0];
			var field2 = component.Fields[1];
			var field3 = component.Fields[2];

			field1.Identifier.Name.Should().Be("value");
			field2.Identifier.Name.Should().Be("test");
			field3.Identifier.Name.Should().Be("other");
		}
	}
}