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

namespace SafetySharp.CSharp
{
	using System;
	using System.Collections.Immutable;
	using Metamodel;
	using Metamodel.Expressions;
	using Metamodel.Statements;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Utilities;

	internal partial class TransformationVisitor
	{
		/// <summary>
		///     Transforms a C# empty statement to the corresponding metamodel empty statement.
		/// </summary>
		/// <param name="node">The C# empty statement that should be transformed.</param>
		public override MetamodelElement VisitEmptyStatement(EmptyStatementSyntax node)
		{
			return EmptyStatement.Default;
		}

		/// <summary>
		///     Transforms a C# expression statement to the corresponding metamodel statement.
		/// </summary>
		/// <param name="node">The C# expression statement that should be transformed.</param>
		public override MetamodelElement VisitExpressionStatement(ExpressionStatementSyntax node)
		{
			Assert.That(node.Expression.CSharpKind() == SyntaxKind.SimpleAssignmentExpression,
						"Unsupported C# expression statement '{0}'.", node.Expression.CSharpKind());

			var assignment = (BinaryExpressionSyntax)node.Expression;
			return new AssignmentStatement((Expression)Visit(assignment.Left), (Expression)Visit(assignment.Right));
		}

		/// <summary>
		///     Called when the visitor visits a ReturnStatementSyntax node.
		/// </summary>
		public override MetamodelElement VisitReturnStatement(ReturnStatementSyntax node)
		{
			if (node.Expression == null)
				return new ReturnStatement(null);

			return new ReturnStatement((Expression)Visit(node.Expression));
		}

		/// <summary>
		///     Transforms a C# if-then-else statement to the corresponding metamodel guarded command.
		/// </summary>
		/// <param name="node">The C# if-then-else statement that should be transformed.</param>
		public override MetamodelElement VisitIfStatement(IfStatementSyntax node)
		{
			var ifCondition = (Expression)Visit(node.Condition);
			var ifStatement = (Statement)Visit(node.Statement);
			var ifClause = new GuardedCommandClause(ifCondition, ifStatement);

			if (node.Else == null)
				return new GuardedCommandStatement(ImmutableArray.Create(ifClause));

			var elseCondition = new UnaryExpression(ifCondition, UnaryOperator.LogicalNot);
			var elseStatement = (Statement)Visit(node.Else.Statement);
			var elseClause = new GuardedCommandClause(elseCondition, elseStatement);

			return new GuardedCommandStatement(ImmutableArray.Create(ifClause, elseClause));
		}
	}
}