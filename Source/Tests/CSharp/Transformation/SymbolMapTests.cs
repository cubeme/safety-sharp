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
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;

	[TestFixture]
	internal class SymbolMapTests
	{
		private SymbolMap _symbolMap;
		private SyntaxNode _syntaxRoot;
		private SemanticModel _semanticModel;

		private void Compile(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);

			_semanticModel = compilation.SemanticModel;
			_syntaxRoot = compilation.SyntaxRoot;

			_symbolMap = SymbolMap.Empty.AddSymbols(_semanticModel);
		}

		private ITypeSymbol GetClassSymbol(string className)
		{
			var classDeclaration = _syntaxRoot.DescendantNodes().OfType<ClassDeclarationSyntax>().First(c => c.Identifier.ValueText == className);
			return (ITypeSymbol)_semanticModel.GetDeclaredSymbol(classDeclaration);
		}

		private IMethodSymbol GetMethodSymbol(ITypeSymbol classSymbol, string methodName)
		{
			return classSymbol.GetMembers(methodName).OfType<IMethodSymbol>().Single();
		}

		[Test]
		public void MethodOfNonComponentClassShouldNotBeMapped()
		{
			Compile("class X { void M() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbol = GetMethodSymbol(classSymbol, "M");

			_symbolMap.IsMapped(methodSymbol).Should().BeFalse();
			Action getReference = () => _symbolMap.GetMethodReference(methodSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}

		[Test]
		public void MethodOfComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component { void M() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbol = GetMethodSymbol(classSymbol, "M");

			_symbolMap.IsMapped(methodSymbol).Should().BeTrue();
			_symbolMap.GetMethodReference(methodSymbol).Should().NotBeNull();
		}

		[Test]
		public void MethodsOfComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component { void M() {} void N() {} }");
			var classSymbol = GetClassSymbol("X");
			var methodSymbolM = GetMethodSymbol(classSymbol, "M");
			var methodSymbolN = GetMethodSymbol(classSymbol, "N");

			_symbolMap.IsMapped(methodSymbolM).Should().BeTrue();
			_symbolMap.IsMapped(methodSymbolM).Should().BeTrue();

			var referenceM = _symbolMap.GetMethodReference(methodSymbolM);
			var referenceN = _symbolMap.GetMethodReference(methodSymbolN);

			referenceM.Should().NotBeNull();
			referenceN.Should().NotBeNull();

			referenceM.Should().NotBe(referenceN);
		}

		[Test]
		public void ComponentClassShouldBeMapped()
		{
			Compile("class X : SafetySharp.Modeling.Component {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeTrue();
			_symbolMap.GetComponentReference(classSymbol).Should().NotBeNull();
		}

		[Test]
		public void ComponentClassesShouldBeMappedAndDifferentReferences()
		{
			Compile("using SafetySharp.Modeling; class Y : Component {} class X : Y {} class Z : Component {}");
			var classSymbolX = GetClassSymbol("X");
			var classSymbolY = GetClassSymbol("Y");
			var classSymbolZ = GetClassSymbol("Z");

			_symbolMap.IsMapped(classSymbolX).Should().BeTrue();
			_symbolMap.IsMapped(classSymbolY).Should().BeTrue();
			_symbolMap.IsMapped(classSymbolZ).Should().BeTrue();

			var referenceX = _symbolMap.GetComponentReference(classSymbolX);
			var referenceY = _symbolMap.GetComponentReference(classSymbolY);
			var referenceZ = _symbolMap.GetComponentReference(classSymbolZ);

			referenceX.Should().NotBeNull();
			referenceY.Should().NotBeNull();
			referenceZ.Should().NotBeNull();

			referenceX.Should().NotBe(referenceY);
			referenceX.Should().NotBe(referenceZ);
			referenceZ.Should().NotBe(referenceY);
		}

		[Test]
		public void InheritedComponentClassShouldBeMapped()
		{
			Compile("class Y : SafetySharp.Modeling.Component {} class X : Y {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeTrue();
			_symbolMap.GetComponentReference(classSymbol).Should().NotBeNull();
		}

		[Test]
		public void NonComponentClassShouldNotBeMapped()
		{
			Compile("class X {}");
			var classSymbol = GetClassSymbol("X");

			_symbolMap.IsMapped(classSymbol).Should().BeFalse();

			Action getReference = () => _symbolMap.GetComponentReference(classSymbol);
			getReference.ShouldThrow<InvalidOperationException>();
		}
	}
}