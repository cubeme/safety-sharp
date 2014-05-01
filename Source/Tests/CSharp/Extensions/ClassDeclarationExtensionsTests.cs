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
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;

	[TestFixture]
	internal class ClassDeclarationExtensionsTests
	{
		private SemanticModel _semanticModel;
		private ClassDeclarationSyntax _classDeclaration;

		private void Compile(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);

			_semanticModel = compilation.SemanticModel;
			_classDeclaration = compilation.SyntaxRoot.DescendantNodesAndSelf()
										   .OfType<ClassDeclarationSyntax>()
										   .Single(classDeclaration => classDeclaration.Identifier.ValueText == "X");
		}

		[Test]
		public void IsComponentDeclarationShouldReturnFalseForNonComponentClassWithBase()
		{
			Compile("class Y {} class X : Y {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeFalse();
		}

		[Test]
		public void IsComponentDeclarationShouldReturnFalseForNonDerivedNonComponentClass()
		{
			Compile("class X {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeFalse();
		}

		[Test]
		public void IsComponentDeclarationShouldReturnTrueForDirectComponentClass()
		{
			Compile("class X : SafetySharp.Modeling.Component {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeTrue();
		}

		[Test]
		public void IsComponentDeclarationShouldReturnTrueForDirectComponentClassWithUsing()
		{
			Compile("using SafetySharp.Modeling; class X : Component {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeTrue();
		}

		[Test]
		public void IsComponentDeclarationShouldReturnTrueForNonDirectComponentClass()
		{
			Compile("class Y : SafetySharp.Modeling.Component {} class X : Y {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeTrue();
		}

		[Test]
		public void IsComponentDeclarationShouldReturnTrueForNonDirectComponentClassWithUsing()
		{
			Compile("using SafetySharp.Modeling; class Y : Component {} class X : Y {}");
			_classDeclaration.IsComponentDeclaration(_semanticModel).Should().BeTrue();
		}

		[Test]
		public void IsDerivedFromShouldReturnFalseForUnderivedBaseTypeWhenClassHasBase()
		{
			Compile("class Y {} class X : Y {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Q").Should().BeFalse();
		}

		[Test]
		public void IsDerivedFromShouldReturnFalseForUnderivedBaseTypeWhenClassHasNoBase()
		{
			Compile("class X {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Q").Should().BeFalse();
		}

		[Test]
		public void IsDerivedFromShouldReturnFalseForUnderivedBaseTypeWhenClassHasTwoBases()
		{
			Compile("class Z {} class Y : Z {} class X : Y {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Q").Should().BeFalse();
		}

		[Test]
		public void IsDerivedFromShouldReturnTrueForDirectBase()
		{
			Compile("class Y {} class X : Y {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Y").Should().BeTrue();
		}

		[Test]
		public void IsDerivedFromShouldReturnTrueWhenBaseIsNotTopLevel()
		{
			Compile("class Z {} class Y : Z {} class X : Y {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Y").Should().BeTrue();
		}

		[Test]
		public void IsDerivedFromShouldReturnTrueWhenBaseIsTwoLevelsUp()
		{
			Compile("class Z {} class Y : Z {} class X : Y {}");
			_classDeclaration.IsDerivedFrom(_semanticModel, "Z").Should().BeTrue();
		}
	}
}