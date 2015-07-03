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

namespace SafetySharp.Runtime.BoundTree
{
	using System;
	using Formulas;
	using Utilities;

	/// <summary>
	///     Visits all <see cref="BoundNode" />s of a bound tree recursively.
	/// </summary>
	public abstract class BoundTreeVisitor
	{
		/// <summary>
		///     Visits the <paramref name="node" />.
		/// </summary>
		/// <param name="node">The <see cref="BoundNode" /> instance that should be visited.</param>
		protected virtual void DefaultVisit(BoundNode node)
		{
		}

		/// <summary>
		///     Visits the <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The <see cref="Expression" /> instance that should be visited.</param>
		protected virtual void DefaultVisit(Expression expression)
		{
			DefaultVisit((BoundNode)expression);
		}

		/// <summary>
		///     Visits the <paramref name="statement" />.
		/// </summary>
		/// <param name="statement">The <see cref="Statement" /> instance that should be visited.</param>
		protected virtual void DefaultVisit(Statement statement)
		{
			DefaultVisit((BoundNode)statement);
		}

		/// <summary>
		///     Visits the <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The <see cref="Formula" /> instance that should be visited.</param>
		protected virtual void DefaultVisit(Formula formula)
		{
			DefaultVisit((BoundNode)formula);
		}

		/// <summary>
		///     Visits an element of type <see cref="ArgumentExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ArgumentExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitArgumentExpression(ArgumentExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitBinaryExpression(BinaryExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BooleanLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BooleanLiteralExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitBooleanLiteralExpression(BooleanLiteralExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitConditionalExpression(ConditionalExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="DoubleLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="DoubleLiteralExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitDoubleLiteralExpression(DoubleLiteralExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="EnumerationLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="EnumerationLiteralExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="FieldExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="FieldExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitFieldExpression(FieldExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="MethodInvocationExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="MethodInvocationExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitMethodInvocationExpression(MethodInvocationExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="IntegerLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="IntegerLiteralExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitIntegerLiteralExpression(IntegerLiteralExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitUnaryExpression(UnaryExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="VariableExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="VariableExpression" /> instance that should be visited.</param>
		protected internal virtual void VisitVariableExpression(VariableExpression expression)
		{
			DefaultVisit(expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BlockStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="BlockStatement" /> instance that should be visited.</param>
		protected internal virtual void VisitBlockStatement(BlockStatement statement)
		{
			DefaultVisit(statement);
		}

		/// <summary>
		///     Visits an element of type <see cref="ChoiceStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ChoiceStatement" /> instance that should be visited.</param>
		protected internal virtual void VisitChoiceStatement(ChoiceStatement statement)
		{
			DefaultVisit(statement);
		}

		/// <summary>
		///     Visits an element of type <see cref="ExpressionStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
		protected internal virtual void VisitExpressionStatement(ExpressionStatement statement)
		{
			DefaultVisit(statement);
		}

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal virtual void VisitAssignmentStatement(AssignmentStatement statement)
		{
			DefaultVisit(statement);
		}

		/// <summary>
		///     Visits an element of type <see cref="ReturnStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
		protected internal virtual void VisitReturnStatement(ReturnStatement statement)
		{
			DefaultVisit(statement);
		}

		/// <summary>
		///     Visits an element of type <see cref="StateFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="StateFormula" /> instance that should be visited.</param>
		protected internal virtual void VisitStateFormula(StateFormula formula)
		{
			DefaultVisit(formula);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="BinaryFormula" /> instance that should be visited.</param>
		protected internal virtual void VisitBinaryFormula(BinaryFormula formula)
		{
			DefaultVisit(formula);
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="UnaryFormula" /> instance that should be visited.</param>
		protected internal virtual void VisitUnaryFormula(UnaryFormula formula)
		{
			DefaultVisit(formula);
		}

		/// <summary>
		///     Visits the <paramref name="node" />.
		/// </summary>
		/// <param name="node">The node that should be visited.</param>
		public void Visit(BoundNode node)
		{
			Requires.NotNull(node, () => node);
			node.Accept(this);
		}
	}
}