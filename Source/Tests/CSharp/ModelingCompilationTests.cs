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

namespace Tests.CSharp
{
	using System;
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.CSharp;
	using SafetySharp.Modeling;

	[TestFixture]
	internal class ModelingCompilationTests
	{
		private static void GetClassDeclaration(string csharpCode, Component component = null)
		{
			csharpCode = String.Format("namespace Tests.CSharp {{ {0} }}", csharpCode);
			var compilation = new TestCompilation(csharpCode);
			var modelingCompilation = new ModelingCompilation(compilation.Compilation);

			if (component == null)
			{
				var assembly = compilation.Compile();
				component = (Component)Activator.CreateInstance(assembly.GetType("Tests.CSharp.TestComponent"));
			}

			var actual = modelingCompilation.GetClassDeclaration(component);
			var expected = compilation.FindClassDeclaration(component.GetType().FullName);

			actual.Should().Be(expected);
		}

		private class TestComponent : Component
		{
		}

		[Test]
		public void GetClassDeclaration_ShouldReturnDeclaration()
		{
			GetClassDeclaration("class TestComponent : Component {}");
		}

		[Test]
		public void GetClassDeclaration_ShouldReturnDeclaration_OtherNamespace()
		{
			GetClassDeclaration("namespace Nested { class TestComponent : Component {} } class TestComponent : Component {}");
		}

		[Test]
		public void GetClassDeclaration_ShouldThrow_MultipleDeclarations()
		{
			Action action = () => GetClassDeclaration("class TestComponent : Component {} class TestComponent : Component {}");
			action.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void GetClassDeclaration_ShouldThrow_OtherNamespace()
		{
			Action action = () => GetClassDeclaration("namespace Nested { class TestComponent : Component {}");
			action.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void GetClassDeclaration_ShouldThrow_UnknownComponentType()
		{
			Action action = () => GetClassDeclaration("class Test : Component {}", new TestComponent());
			action.ShouldThrow<InvalidOperationException>();
		}
	}
}