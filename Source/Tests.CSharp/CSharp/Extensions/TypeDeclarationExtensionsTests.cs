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

namespace Tests.CSharp.Extensions
{
	using System;

	namespace TypeDeclarationExtensionsTests
	{
		using FluentAssertions;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;

		[TestFixture]
		internal class IsComponentDeclarationMethod
		{
			private static bool IsComponent(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);
				var classDeclaration = compilation.FindClassDeclaration("X");
				return classDeclaration.IsComponentDeclaration(compilation.SemanticModel);
			}

			[Test]
			public void ReturnsFalseForNonComponentClass()
			{
				IsComponent("class X {}").Should().BeFalse();
				IsComponent("class Y {} class X : Y {}").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForComponentClass()
			{
				IsComponent("class X : Component {}").Should().BeTrue();
				IsComponent("class Y : Component {} class X : Y {}").Should().BeTrue();
			}
		}

		[TestFixture]
		internal class IsComponentInterfaceDeclarationMethod
		{
			private static bool IsComponentInterface(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);
				var interfaceDeclaration = compilation.FindInterfaceDeclaration("X");
				return interfaceDeclaration.IsComponentInterfaceDeclaration(compilation.SemanticModel);
			}

			[Test]
			public void ReturnsFalseForNonComponentInterface()
			{
				IsComponentInterface("interface X {}").Should().BeFalse();
				IsComponentInterface("interface Y {} interface X : Y {}").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForComponentInterface()
			{
				IsComponentInterface("interface X : IComponent {}").Should().BeTrue();
				IsComponentInterface("interface Y {} interface X : IComponent, Y {}").Should().BeTrue();
				IsComponentInterface("interface Y {} interface X : Y, IComponent {}").Should().BeTrue();
				IsComponentInterface("interface Q {} interface Z : IComponent, Q {} interface Y : Z {} interface X : Y {}").Should().BeTrue();
				IsComponentInterface("interface Q {} interface Z : Q, IComponent {} interface Y : Z {} interface X : Y {}").Should().BeTrue();
			}
		}
	}
}