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
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;

	internal abstract class TransformationVisitorTests
	{
		protected MetamodelReference<FieldDeclaration> BoolFieldReference { get; private set; }
		protected MetamodelReference<FieldDeclaration> IntFieldReference { get; private set; }

		[SetUp]
		public void Setup()
		{
			BoolFieldReference = null;
			IntFieldReference = null;
		}

		private void CheckElementTree(MetamodelElement expectedElement, string csharpCode, Func<BlockSyntax, SyntaxNode> projection)
		{
			var actualElement = Transform(csharpCode, projection);
			actualElement.Should().Be(expectedElement);
		}

		protected void Test(Expression expectedExpression, string csharpExpression)
		{
			CheckElementTree(expectedExpression, csharpExpression,
							 block => ((ExpressionStatementSyntax)block.Statements.First()).Expression);
		}

		protected void Test(Statement expectedStatement, string csharpStatement)
		{
			CheckElementTree(expectedStatement.AsBlockStatement(), csharpStatement, block => block);
		}

		private MetamodelElement Transform(string csharpCode, Func<BlockSyntax, SyntaxNode> projection)
		{
			csharpCode = @"
class C : SafetySharp.Modeling.Component 
{
	private bool boolField; 
    private int intField;
	void M()
	{
		" + csharpCode + @"
	}
}";
			var compilation = new TestCompilation(csharpCode);

			var methodBody = compilation.SyntaxTree.DescendantNodes<BlockSyntax>().Single();

			var symbolMap = SymbolMap.Empty.AddSymbols(compilation.SemanticModel);
			BoolFieldReference = symbolMap.GetFieldReference(compilation.FindFieldSymbol("C", "boolField"));
			IntFieldReference = symbolMap.GetFieldReference(compilation.FindFieldSymbol("C", "intField"));

			var visitor = new TransformationVisitor(compilation.SemanticModel, symbolMap);
			return visitor.Visit(projection(methodBody));
		}

		protected MetamodelElement TransformExpression(string csharpExpression)
		{
			return Transform(csharpExpression, block => ((ExpressionStatementSyntax)block.Statements.First()).Expression);
		}

		protected MetamodelElement TransformStatement(string csharpStatement)
		{
			var statement = (BlockStatement)Transform(csharpStatement, block => block);
			if (statement.Statements.Length != 1)
				throw new InvalidOperationException("More than one statement in block.");

			return statement.Statements[0];
		}
	}
}