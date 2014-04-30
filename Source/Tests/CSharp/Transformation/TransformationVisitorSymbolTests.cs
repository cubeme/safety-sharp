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
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel.Declarations;

	[TestFixture]
	public class TransformationVisitorSymbolTests
	{
		[Test]
		public void ComponentDeclaration()
		{
			var compilation = CSharpUtils.Compile("class C { public void M() {} }");
			var symbolMap = new SymbolMap(compilation);
			var syntaxTree = compilation.SyntaxTrees.First();
			var rootNode = syntaxTree.GetRoot();
			var semanticModel = compilation.GetSemanticModel(syntaxTree);

			var visitor = new TransformationVisitor(semanticModel, symbolMap);
			var component = visitor.Visit(rootNode) as ComponentDeclaration;

			component.Should().NotBeNull("The transformed element must be a component declaration.");

			var method = rootNode.DescendantNodes().OfType<MethodDeclarationSyntax>().First();
			var methodSymbol = semanticModel.GetDeclaredSymbol(method);
			var methodReference = symbolMap.GetMethodReference(methodSymbol);

			component.Methods[0].Should().Be(methodReference);
		}
	}
}