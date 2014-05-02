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
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;

	[TestFixture]
	internal class SymbolExtensionsTests
	{
		private void Test(string csharpCode, string fullName)
		{
			var compilation = new TestCompilation(csharpCode);
			var classDeclaration = compilation.SyntaxRoot.DescendantNodesAndSelf()
											  .OfType<ClassDeclarationSyntax>()
											  .Single(c => c.Identifier.ValueText == "X");

			var classSymbol = compilation.SemanticModel.GetDeclaredSymbol(classDeclaration);
			classSymbol.GetFullName().Should().Be(fullName);
		}

		[Test]
		public void ClassAtTopLevel()
		{
			Test("class X {}", "X");
		}

		[Test]
		public void ClassNestedInsideNamespaces()
		{
			Test("namespace Test.Other { class X {} }", "Test.Other.X");
		}

		[Test]
		public void ClassNestedInsideNestedNamespaces()
		{
			Test("namespace Test namespace Other {{ class X {} }}", "Test.Other.X");
		}

		[Test]
		public void ClassNestedInsideUnnestedNamespace()
		{
			Test("namespace Test { class X {} }", "Test.X");
		}

		[Test]
		public void ClassNestedWithinClassAtTopLevel()
		{
			Test("class Y { class X {}}", "Y+X");
		}

		[Test]
		public void ClassNestedWithinClassInsideNamespaces()
		{
			Test("namespace Test.Other { class Y { class X {}} }", "Test.Other.Y+X");
		}

		[Test]
		public void ClassNestedWithinClassInsideNestedNamespaces()
		{
			Test("namespace Test namespace Other {{ class Y { class X {}} }}", "Test.Other.Y+X");
		}

		[Test]
		public void ClassWithinClassNestedInsideUnnestedNamespace()
		{
			Test("namespace Test { class Y { class X {}} }", "Test.Y+X");
		}
	}
}