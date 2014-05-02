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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Metamodel;
	using Metamodel.Expressions;
	using Metamodel.Statements;
	using Microsoft.CodeAnalysis;
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
		///     Transforms a C# block statement to the corresponding metamodel block statement.
		/// </summary>
		/// <param name="node">The C# block statement that should be transformed.</param>
		public override MetamodelElement VisitBlock(BlockSyntax node)
		{
			return new BlockStatement(node.Statements.Select(s => (Statement)Visit(s)).ToImmutableArray());
		}

		/// <summary>
		///     Transforms a C# expression statement to the corresponding metamodel statement.
		/// </summary>
		/// <param name="node">The C# expression statement that should be transformed.</param>
		public override MetamodelElement VisitExpressionStatement(ExpressionStatementSyntax node)
		{
			// The metamodel does not support expressions embedded into statements. We therefore have to
			// create the appropriate metamodel statement type depending on the type and structure of the 
			// C# expression.
			switch (node.Expression.CSharpKind())
			{
				case SyntaxKind.SimpleAssignmentExpression:
					var assignment = node.Expression as BinaryExpressionSyntax;
					return new AssignmentStatement((Expression)Visit(assignment.Left), (Expression)Visit(assignment.Right));
				case SyntaxKind.InvocationExpression:
					var symbolInfo = _semanticModel.GetSymbolInfo(node.Expression);
					var symbol = symbolInfo.Symbol;

					Assert.NotNull(symbol, "Unable to determine symbol for invocation expression '{0}'.", node.Expression);

					var invocation = node.Expression as InvocationExpressionSyntax;
					var arguments = invocation.ArgumentList.Arguments;
					var methodSymbol = symbol as IMethodSymbol;

					if (methodSymbol != null)
					{
						var compareTarget = methodSymbol;
						if (methodSymbol.OriginalDefinition != null)
							compareTarget = methodSymbol.OriginalDefinition;

						if (compareTarget.Equals(KnownSymbols.ChooseFromValuesMethod))
						{
							var assignmentTarget = (Expression)Visit(arguments[0].Expression);
							var expressions = arguments.Skip(1).Select(argument => (Expression)Visit(argument.Expression));
							var statements = expressions.Select(expression => new AssignmentStatement(assignmentTarget, expression));
							var clauses = statements.Select(statement => new GuardedCommandClause(BooleanLiteral.True, statement));
							return new GuardedCommandStatement(clauses.ToImmutableArray());
						}

						Assert.NotReached("Unsupported C# Choose call: '{0}'.", node.Expression);
					}

					Assert.NotReached("Unsupported C# method call: '{0}'.", node.Expression);
					return null;
				default:
					Assert.NotReached("Unsupported C# expression statement '{0}'.", node.Expression.CSharpKind());
					return null;
			}
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