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

	namespace NamespaceOrTypeSymbolExtensionsTests
	{
		using System.Linq;
		using FluentAssertions;
		using Microsoft.CodeAnalysis.CSharp;
		using Microsoft.CodeAnalysis.CSharp.Syntax;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;

		[TestFixture]
		internal class GetFullNameMethod
		{
			private static string GetFullName(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);

				// We can't use compilation.FindClassDeclaration() here as the implementation of that helper method
				// depends on the GetFullName() extension method which we're currently testing...
				var classDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<ClassDeclarationSyntax>()
					.Single(c => c.Identifier.ValueText == "X");

				var classSymbol = compilation.SemanticModel.GetDeclaredSymbol(classDeclaration);
				return classSymbol.GetFullName();
			}

			[Test]
			public void ReturnsClassNameForClassInGlobalNamespace()
			{
				GetFullName("class X {}").Should().Be("X");
			}

			[Test]
			public void ReturnsNamespacedClassNameForClassInNamespace()
			{
				GetFullName("namespace Test { class X {} }").Should().Be("Test.X");
				GetFullName("namespace Test.Other { class X {} }").Should().Be("Test.Other.X");
				GetFullName("namespace Test { namespace Other { class X {} }}").Should().Be("Test.Other.X");
			}

			[Test]
			public void ReturnsNestedClassNameForNestedClass()
			{
				GetFullName("class Y { class X {}}").Should().Be("Y+X");
				GetFullName("namespace Test.Other { class Y { class X {}} }").Should().Be("Test.Other.Y+X");
				GetFullName("namespace Test { namespace Other { class Y { class X {}} }}").Should().Be("Test.Other.Y+X");
				GetFullName("namespace Test { class Y { class X {}} }").Should().Be("Test.Y+X");
			}
		}
	}
}