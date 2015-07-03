// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace SafetySharp.Transformation
{
	using System;
	using System.Linq;
	using Runtime.BoundTree;

	/// <summary>
	///     A base class for rewriting trees of <see cref="BoundNode" />s.
	/// </summary>
	internal abstract class BoundTreeRewriter : BoundTreeVisitor<BoundNode>
	{
		/// <summary>
		///     Visits an element of type <see cref="ArgumentExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ArgumentExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitArgumentExpression(ArgumentExpression expression)
		{
			return new ArgumentExpression((Expression)Visit(expression.Expression), expression.RefKind);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitBinaryExpression(BinaryExpression expression)
		{
			return new BinaryExpression(expression.Operator, (Expression)Visit(expression.LeftOperand), (Expression)Visit(expression.RightOperand));
		}

		/// <summary>
		///     Visits an element of type <see cref="BooleanLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BooleanLiteralExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitConditionalExpression(ConditionalExpression expression)
		{
			return new ConditionalExpression((Expression)Visit(expression.Condition),
				(Expression)Visit(expression.TrueBranch), (Expression)Visit(expression.FalseBranch));
		}

		/// <summary>
		///     Visits an element of type <see cref="DoubleLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="DoubleLiteralExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="EnumerationLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="EnumerationLiteralExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="FieldExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="FieldExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitFieldExpression(FieldExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="MethodInvocationExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="MethodInvocationExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitMethodInvocationExpression(MethodInvocationExpression expression)
		{
			return new MethodInvocationExpression(expression.Method, expression.Arguments.Select(Visit).Cast<ArgumentExpression>().ToArray());
		}

		/// <summary>
		///     Visits an element of type <see cref="IntegerLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="IntegerLiteralExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitUnaryExpression(UnaryExpression expression)
		{
			return new UnaryExpression(expression.Operator, (Expression)Visit(expression.Operand));
		}

		/// <summary>
		///     Visits an element of type <see cref="VariableExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="VariableExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitVariableExpression(VariableExpression expression)
		{
			return expression;
		}

		/// <summary>
		///     Visits an element of type <see cref="BlockStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="BlockStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitBlockStatement(BlockStatement statement)
		{
			return new BlockStatement(statement.Statements.Select(Visit).Cast<Statement>().ToArray());
		}

		/// <summary>
		///     Visits an element of type <see cref="ChoiceStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ChoiceStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitChoiceStatement(ChoiceStatement statement)
		{
			return new ChoiceStatement(statement.Guards.Select(Visit).Cast<Expression>().ToArray(),
				statement.Statements.Select(Visit).Cast<Statement>().ToArray(), statement.IsDeterministic);
		}

		/// <summary>
		///     Visits an element of type <see cref="ExpressionStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitExpressionStatement(ExpressionStatement statement)
		{
			return new ExpressionStatement((Expression)Visit(statement.Expression));
		}

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitAssignmentStatement(AssignmentStatement statement)
		{
			return new AssignmentStatement((Expression)Visit(statement.AssignmentTarget), (Expression)Visit(statement.Expression));
		}

		/// <summary>
		///     Visits an element of type <see cref="ReturnStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitReturnStatement(ReturnStatement statement)
		{
			return new ReturnStatement((Expression)Visit(statement.Expression));
		}
	}
}