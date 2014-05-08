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
	using System.Collections.Immutable;
	using System.Linq;
	using FluentAssertions;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using NUnit.Framework;
	using SafetySharp.CSharp.Extensions;
	using SafetySharp.CSharp.Transformation;
	using SafetySharp.Metamodel;
	using SafetySharp.Metamodel.Declarations;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;

	[TestFixture]
	internal class MethodTransformationStatementTests
	{
		private IMetamodelReference<FieldDeclaration> _boolFieldReference;
		private IMetamodelReference<FieldDeclaration> _intFieldReference;

		private MetamodelElement Transform(string csharpCode, string returnType = "void")
		{
			csharpCode = @"
class C : SafetySharp.Modeling.Component 
{
	private bool boolField; 
    private int intField;
	" + returnType + @" M()
	{
		" + csharpCode + @";
	}
}";
			var compilation = new TestCompilation(csharpCode);
			var expression = compilation.SyntaxRoot.DescendantNodes<BlockSyntax>().Single().Statements[0];

			var symbolMap = new SymbolMap(compilation.Compilation);
			_boolFieldReference = symbolMap.GetFieldReference(compilation.FindFieldSymbol("C", "boolField"));
			_intFieldReference = symbolMap.GetFieldReference(compilation.FindFieldSymbol("C", "intField"));

			var visitor = new MethodTransformation(compilation.SemanticModel, symbolMap);
			return visitor.Visit(expression);
		}

		private void Test(Statement expectedStatement, string csharpStatement, string returnType = "void")
		{
			var actualStatement = Transform(csharpStatement, returnType);
			actualStatement.Should().Be(expectedStatement);
		}

		[Test]
		public void AssignmentStatement_SimpleExpression()
		{
			var actual = Transform("boolField = true;");
			var expected = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), BooleanLiteral.True);
			actual.Should().Be(expected);
		}

		[Test]
		public void AssignmentStatement_BinaryExpression()
		{
			var actual = Transform("boolField = true || false;");
			var expression = new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False);
			var expected = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), expression);
			actual.Should().Be(expected);
		}

		[Test]
		public void ChooseFromValues_TwoValues()
		{
			var actual = Transform("Choose(out boolField, true, false);");

			var assignment1 = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), BooleanLiteral.True);
			var assignment2 = new AssignmentStatement(new FieldAccessExpression(_boolFieldReference), BooleanLiteral.False);

			var case1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
			var case2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);

			var expected = new GuardedCommandStatement(ImmutableArray.Create(case1, case2));
			actual.Should().Be(expected);
		}

		[Test]
		public void ChooseFromValues_FourValues()
		{
			var actual = Transform("Choose(out intField, -17, 0, 33, 127);");

			var minusSeventeen = new UnaryExpression(new IntegerLiteral(17), UnaryOperator.Minus);
			var assignment1 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), minusSeventeen);
			var assignment2 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(0));
			var assignment3 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(33));
			var assignment4 = new AssignmentStatement(new FieldAccessExpression(_intFieldReference), new IntegerLiteral(127));

			var case1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
			var case2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);
			var case3 = new GuardedCommandClause(BooleanLiteral.True, assignment3);
			var case4 = new GuardedCommandClause(BooleanLiteral.True, assignment4);

			var expected = new GuardedCommandStatement(ImmutableArray.Create(case1, case2, case3, case4));
			actual.Should().Be(expected);
		}

		[Test]
		public void EmptyStatement()
		{
			Test(new EmptyStatement(), ";");
		}

		[Test]
		public void ReturnStatements()
		{
			Test(new ReturnStatement(null), "return;");
			Test(new ReturnStatement(new IntegerLiteral(1)), "return 1;", "int");
			Test(new ReturnStatement(BooleanLiteral.False), "return false;", "bool");
		}

		[Test]
		public void GuardedCommands()
		{
			var ifClause = new GuardedCommandClause(BooleanLiteral.True, new EmptyStatement());
			var elseClause = new GuardedCommandClause(new UnaryExpression(BooleanLiteral.True, UnaryOperator.LogicalNot), new ReturnStatement(null));

			Test(new GuardedCommandStatement(ImmutableArray.Create(ifClause)), "if (true) ;");
			Test(new GuardedCommandStatement(ImmutableArray.Create(ifClause, elseClause)), "if (true) ; else return;");
		}
	}
}
