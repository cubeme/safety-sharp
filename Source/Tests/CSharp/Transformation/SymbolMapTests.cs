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

		private void CreateSymbolMap(string csharpCode)
		{
			var compilation = new TestCompilation(csharpCode);

			_semanticModel = compilation.SemanticModel;
			_syntaxRoot = compilation.SyntaxRoot;

			_symbolMap = new SymbolMap(compilation.Compilation);
		}

		private ISymbol GetClassSymbol(string className)
		{
			var classDeclaration = _syntaxRoot.DescendantNodes()
											  .OfType<ClassDeclarationSyntax>()
											  .First(c => c.Identifier.ValueText == className);

			return _semanticModel.GetDeclaredSymbol(classDeclaration);
		}

		[Test]
		public void CollectClasses()
		{
			CreateSymbolMap(
				"using SafetySharp.Modeling; class X : Component {} class Y : SafetySharp.Modeling.Component { class Z : SafetySharp.Modeling.Component {} }");
			var classX = GetClassSymbol("X");
			var classY = GetClassSymbol("Y");
			var classZ = GetClassSymbol("Z");

			_symbolMap.IsMapped(classX).Should().BeTrue();
			_symbolMap.IsMapped(classY).Should().BeTrue();
			_symbolMap.IsMapped(classZ).Should().BeTrue();

			var referenceX = _symbolMap.GetComponentReference(classX);
			var referenceY = _symbolMap.GetComponentReference(classY);
			var referenceZ = _symbolMap.GetComponentReference(classZ);

			(referenceX == referenceY).Should().BeFalse();
			(referenceX == referenceZ).Should().BeFalse();
			(referenceZ == referenceY).Should().BeFalse();
		}
	}
}