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
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;

	[TestFixture]
	internal class FieldDeclarationExtensionsTests
	{
		private static void ShouldBeComponentField(string csharpCode, string fieldName, bool shouldBeComponentField = true)
		{
			var compilation = new TestCompilation("using SafetySharp.Modeling; " + csharpCode);
			var fieldDeclaration = compilation
				.SyntaxRoot
				.DescendantNodesAndSelf<FieldDeclarationSyntax>()
				.Single(field => field.Declaration.Variables.Any(v => v.Identifier.ValueText == fieldName));

			fieldDeclaration.IsComponentField(compilation.SemanticModel).Should().Be(shouldBeComponentField);
		}

		private static void ShouldNotBeComponentField(string csharpCode, string fieldName)
		{
			ShouldBeComponentField(csharpCode, fieldName, false);
		}

		[Test]
		public void IsComponentField_False_NonComponentField()
		{
			ShouldNotBeComponentField("class X : Component { int x; }", "x");
		}

		[Test]
		public void IsComponentField_True_BaseClassComponentField()
		{
			ShouldBeComponentField("class X : Component { Component x; }", "x");
		}

		[Test]
		public void IsComponentField_True_BaseInterfaceComponentField()
		{
			ShouldBeComponentField("class X : Component { IComponent x; }", "x");
		}

		[Test]
		public void IsComponentField_True_DerivedClassComponentField()
		{
			ShouldBeComponentField("class Y : Component {} class X : Component { Y x; }", "x");
		}

		[Test]
		public void IsComponentField_True_DerivedInterfaceComponentField()
		{
			ShouldBeComponentField("interface Y : IComponent {} class X : Component { Y x; }", "x");
		}
	}
}