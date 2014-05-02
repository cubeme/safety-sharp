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
	using FluentAssertions;
	using NUnit.Framework;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;

	[TestFixture]
	internal class TransformationVisitorStatementTests : TransformationVisitorTests
	{
		[Test]
		public void AssignmentStatement_SimpleExpression()
		{
			var actual = TransformStatement("boolField = true;");
			var expected = new AssignmentStatement(new FieldAccessExpression(BoolFieldReference), BooleanLiteral.True);
			actual.Should().Be(expected);
		}

		[Test]
		public void AssignmentStatement_BinaryExpression()
		{
			var actual = TransformStatement("boolField = true || false;");
			var expression = new BinaryExpression(BooleanLiteral.True, BinaryOperator.LogicalOr, BooleanLiteral.False);
			var expected = new AssignmentStatement(new FieldAccessExpression(BoolFieldReference), expression);
			actual.Should().Be(expected);
		}

		[Test]
		public void ChooseFromValues_TwoValues()
		{
			var actual = TransformStatement("Choose(out boolField, true, false);");

			var assignment1 = new AssignmentStatement(new FieldAccessExpression(BoolFieldReference), BooleanLiteral.True);
			var assignment2 = new AssignmentStatement(new FieldAccessExpression(BoolFieldReference), BooleanLiteral.False);

			var case1 = new GuardedCommandClause(BooleanLiteral.True, assignment1);
			var case2 = new GuardedCommandClause(BooleanLiteral.True, assignment2);

			var expected = new GuardedCommandStatement(ImmutableArray.Create(case1, case2));
			actual.Should().Be(expected);
		}

		[Test]
		public void ChooseFromValues_FourValues()
		{
			var actual = TransformStatement("Choose(out intField, -17, 0, 33, 127);");

			var minusSeventeen = new UnaryExpression(new IntegerLiteral(17), UnaryOperator.Minus);
			var assignment1 = new AssignmentStatement(new FieldAccessExpression(IntFieldReference), minusSeventeen);
			var assignment2 = new AssignmentStatement(new FieldAccessExpression(IntFieldReference), new IntegerLiteral(0));
			var assignment3 = new AssignmentStatement(new FieldAccessExpression(IntFieldReference), new IntegerLiteral(33));
			var assignment4 = new AssignmentStatement(new FieldAccessExpression(IntFieldReference), new IntegerLiteral(127));

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
			Test(new ReturnStatement(new IntegerLiteral(1)), "return 1;");
			Test(new ReturnStatement(BooleanLiteral.False), "return false;");
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
