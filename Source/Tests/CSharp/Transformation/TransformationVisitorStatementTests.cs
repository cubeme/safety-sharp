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
	using NUnit.Framework;
	using SafetySharp.Metamodel.Expressions;
	using SafetySharp.Metamodel.Statements;

	[TestFixture]
	internal class TransformationVisitorStatementTests : TransformationVisitorTests
	{
		[Test]
		public void AssignmentStatements()
		{
			Test(new AssignmentStatement(new IntegerLiteral(1), new IntegerLiteral(5)), "1 = 5");

			var binaryExpression = new BinaryExpression(new IntegerLiteral(5), BinaryOperator.Add, new IntegerLiteral(2));
			Test(new AssignmentStatement(new IntegerLiteral(1), binaryExpression), "1 = 5 + 2");
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
