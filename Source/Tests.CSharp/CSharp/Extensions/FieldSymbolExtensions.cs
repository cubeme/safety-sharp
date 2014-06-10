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

	namespace FieldSymbolExtensionsTests
	{
		using System.Linq;
		using FluentAssertions;
		using Microsoft.CodeAnalysis;
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
				var typeDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<TypeDeclarationSyntax>()
					.Single(c => c.Identifier.ValueText == "X");

				var typeSymbol = compilation.SemanticModel.GetDeclaredSymbol(typeDeclaration);
				return typeSymbol.GetMembers().OfType<IFieldSymbol>().Single(field => field.Name == "f").GetFullName();
			}

			[Test]
			public void ReturnsFieldNameForGenericType()
			{
				GetFullName("class X<T1, T2> { int f; }").Should().Be("X<T1, T2>.f");
				GetFullName("struct X<T1, T2> { int f; }").Should().Be("X<T1, T2>.f");
			}

			[Test]
			public void ReturnsFieldNameForNestedTypes()
			{
				GetFullName("class Y { class X { int f; }}").Should().Be("Y+X.f");
				GetFullName("namespace Test.Other { class Y { class X { int f; }} }").Should().Be("Test.Other.Y+X.f");
				GetFullName("namespace Test.Other { struct Y { class X { int f; }} }").Should().Be("Test.Other.Y+X.f");
				GetFullName("namespace Test.Other { class Y { struct X { int f; }} }").Should().Be("Test.Other.Y+X.f");
				GetFullName("namespace Test.Other { struct Y { struct X { int f; }} }").Should().Be("Test.Other.Y+X.f");
				GetFullName("namespace Test { namespace Other { class Y { class X { int f; }} }}").Should().Be("Test.Other.Y+X.f");
				GetFullName("namespace Test { class Y { class X { int f; }} }").Should().Be("Test.Y+X.f");
			}

			[Test]
			public void ReturnsFieldNameForTypeInGlobalNamespace()
			{
				GetFullName("class X { int f; }").Should().Be("X.f");
				GetFullName("struct X { int f; }").Should().Be("X.f");
			}

			[Test]
			public void ReturnsFieldNameForTypeInNamespace()
			{
				GetFullName("namespace Test { class X { private int f; } }").Should().Be("Test.X.f");
				GetFullName("namespace Test.Other { class X { int f; } }").Should().Be("Test.Other.X.f");
				GetFullName("namespace Test { namespace Other { class X { int f; } }}").Should().Be("Test.Other.X.f");
				GetFullName("namespace Test { struct X { private int f; } }").Should().Be("Test.X.f");
				GetFullName("namespace Test.Other { struct X { int f; } }").Should().Be("Test.Other.X.f");
				GetFullName("namespace Test { namespace Other { struct X { int f; } }}").Should().Be("Test.Other.X.f");
			}
		}
	}
}