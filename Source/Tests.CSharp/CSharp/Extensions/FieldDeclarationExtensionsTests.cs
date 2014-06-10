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

	namespace FieldDeclarationExtensionsTests
	{
		using System.Linq;
		using FluentAssertions;
		using Microsoft.CodeAnalysis.CSharp.Syntax;
		using NUnit.Framework;
		using SafetySharp.CSharp.Extensions;

		[TestFixture]
		internal class IsComponentFieldMethod
		{
			private static bool IsComponentField(string csharpCode, string fieldName)
			{
				var compilation = new TestCompilation(csharpCode);
				var fieldDeclaration = compilation
					.SyntaxRoot
					.DescendantNodesAndSelf<FieldDeclarationSyntax>()
					.Single(field => field.Declaration.Variables.Any(v => v.Identifier.ValueText == fieldName));

				return fieldDeclaration.IsComponentField(compilation.SemanticModel);
			}

			[Test]
			public void ReturnsFalseForNonComponentFields()
			{
				IsComponentField("class X : Component { int x; }", "x").Should().BeFalse();
				IsComponentField("class X : Component { bool x; }", "x").Should().BeFalse();
				IsComponentField("class X : Component { decimal x; }", "x").Should().BeFalse();
			}

			[Test]
			public void ReturnsTrueForComponentFields()
			{
				IsComponentField("class X : Component { Component x; }", "x").Should().BeTrue();
				IsComponentField("class X : Component { IComponent x; }", "x").Should().BeTrue();
				IsComponentField("class Y : Component {} class X : Component { Y x; }", "x").Should().BeTrue();
				IsComponentField("interface Y : IComponent {} class X : Component { Y x; }", "x").Should().BeTrue();
			}
		}
	}
}