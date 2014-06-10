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
			private static string GetClassName(string csharpCode)
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

			private static string GetInterfaceName(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);

				// We can't use compilation.FindInterfaceDeclaration() here as the implementation of that helper method
				// depends on the GetFullName() extension method which we're currently testing...
				var interfaceDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<InterfaceDeclarationSyntax>()
					.Single(c => c.Identifier.ValueText == "X");

				var interfaceSymbol = compilation.SemanticModel.GetDeclaredSymbol(interfaceDeclaration);
				return interfaceSymbol.GetFullName();
			}

			private static string GetStructName(string csharpCode)
			{
				var compilation = new TestCompilation(csharpCode);

				// We can't use compilation.FindStructDeclaration() here as the implementation of that helper method
				// depends on the GetFullName() extension method which we're currently testing...
				var structDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<StructDeclarationSyntax>()
					.Single(c => c.Identifier.ValueText == "X");

				var structSymbol = compilation.SemanticModel.GetDeclaredSymbol(structDeclaration);
				return structSymbol.GetFullName();
			}

			[Test]
			public void ReturnsClassNameForClassInGlobalNamespace()
			{
				GetClassName("class X {}").Should().Be("X");
			}

			[Test]
			public void ReturnsClassNameForClassInNamespace()
			{
				GetClassName("namespace Test { class X {} }").Should().Be("Test.X");
				GetClassName("namespace Test.Other { class X {} }").Should().Be("Test.Other.X");
				GetClassName("namespace Test { namespace Other { class X {} }}").Should().Be("Test.Other.X");
			}

			[Test]
			public void ReturnsClassNameForGenericClass()
			{
				GetClassName("class X<T1, T2> {}").Should().Be("X<T1, T2>");
			}

			[Test]
			public void ReturnsClassNameForNestedClass()
			{
				GetClassName("class Y { class X {}}").Should().Be("Y+X");
				GetClassName("namespace Test.Other { class Y { class X {}} }").Should().Be("Test.Other.Y+X");
				GetClassName("namespace Test.Other { struct Y { class X {}} }").Should().Be("Test.Other.Y+X");
				GetClassName("namespace Test { namespace Other { class Y { class X {}} }}").Should().Be("Test.Other.Y+X");
				GetClassName("namespace Test { class Y { class X {}} }").Should().Be("Test.Y+X");
			}

			[Test]
			public void ReturnsInterfaceNameForInterfaceInGlobalNamespace()
			{
				GetInterfaceName("interface X {}").Should().Be("X");
			}

			[Test]
			public void ReturnsInterfaceNameForInterfaceInNamespace()
			{
				GetInterfaceName("namespace Test { interface X {} }").Should().Be("Test.X");
				GetInterfaceName("namespace Test.Other { interface X {} }").Should().Be("Test.Other.X");
				GetInterfaceName("namespace Test { namespace Other { interface X {} }}").Should().Be("Test.Other.X");
			}

			[Test]
			public void ReturnsInterfaceNameForGenericInterface()
			{
				GetInterfaceName("interface X<T1, T2> {}").Should().Be("X<T1, T2>");
			}

			[Test]
			public void ReturnsInterfaceNameForNestedInterface()
			{
				GetInterfaceName("class Y { interface X {}}").Should().Be("Y+X");
				GetInterfaceName("namespace Test.Other { class Y { interface X {}} }").Should().Be("Test.Other.Y+X");
				GetInterfaceName("namespace Test.Other { struct Y { interface X {}} }").Should().Be("Test.Other.Y+X");
				GetInterfaceName("namespace Test { namespace Other { class Y { interface X {}} }}").Should().Be("Test.Other.Y+X");
				GetInterfaceName("namespace Test { class Y { interface X {}} }").Should().Be("Test.Y+X");
			}

			[Test]
			public void ReturnsStructNameForStructInGlobalNamespace()
			{
				GetStructName("struct X {}").Should().Be("X");
			}

			[Test]
			public void ReturnsStructNameForStructInNamespace()
			{
				GetStructName("namespace Test { struct X {} }").Should().Be("Test.X");
				GetStructName("namespace Test.Other { struct X {} }").Should().Be("Test.Other.X");
				GetStructName("namespace Test { namespace Other { struct X {} }}").Should().Be("Test.Other.X");
			}

			[Test]
			public void ReturnsStructNameForGenericStruct()
			{
				GetStructName("struct X<T1, T2> {}").Should().Be("X<T1, T2>");
			}

			[Test]
			public void ReturnsStructNameForNestedStruct()
			{
				GetStructName("class Y { struct X {}}").Should().Be("Y+X");
				GetStructName("namespace Test.Other { class Y { struct X {}} }").Should().Be("Test.Other.Y+X");
				GetStructName("namespace Test.Other { struct Y { struct X {}} }").Should().Be("Test.Other.Y+X");
				GetStructName("namespace Test { namespace Other { class Y { struct X {}} }}").Should().Be("Test.Other.Y+X");
				GetStructName("namespace Test { class Y { struct X {}} }").Should().Be("Test.Y+X");
			}
		}
	}
}