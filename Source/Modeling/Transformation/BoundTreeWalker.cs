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
	using Runtime.BoundTree;
	using Runtime.Formulas;

	/// <summary>
	///     A base class for visiting all <see cref="BoundNode" />s within a tree.
	/// </summary>
	internal abstract class BoundTreeWalker : BoundTreeVisitor
	{
		/// <summary>
		///     Visits an element of type <see cref="ArgumentExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ArgumentExpression" /> instance that should be visited.</param>
		protected internal override void VisitArgumentExpression(ArgumentExpression expression)
		{
			Visit(expression.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal override void VisitBinaryExpression(BinaryExpression expression)
		{
			Visit(expression.LeftOperand);
			Visit(expression.RightOperand);
		}

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal override void VisitConditionalExpression(ConditionalExpression expression)
		{
			Visit(expression.Condition);
			Visit(expression.TrueBranch);
			Visit(expression.FalseBranch);
		}

		/// <summary>
		///     Visits an element of type <see cref="MethodInvocationExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="MethodInvocationExpression" /> instance that should be visited.</param>
		protected internal override void VisitMethodInvocationExpression(MethodInvocationExpression expression)
		{
			foreach (var argument in expression.Arguments)
				Visit(argument);
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal override void VisitUnaryExpression(UnaryExpression expression)
		{
			Visit(expression.Operand);
		}

		/// <summary>
		///     Visits an element of type <see cref="BlockStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="BlockStatement" /> instance that should be visited.</param>
		protected internal override void VisitBlockStatement(BlockStatement statement)
		{
			foreach (var containedStatement in statement.Statements)
				Visit(containedStatement);
		}

		/// <summary>
		///     Visits an element of type <see cref="ChoiceStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ChoiceStatement" /> instance that should be visited.</param>
		protected internal override void VisitChoiceStatement(ChoiceStatement statement)
		{
			foreach (var guard in statement.Guards)
				Visit(guard);

			foreach (var guardedStatement in statement.Statements)
				Visit(guardedStatement);
		}

		/// <summary>
		///     Visits an element of type <see cref="ExpressionStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
		protected internal override void VisitExpressionStatement(ExpressionStatement statement)
		{
			Visit(statement.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal override void VisitAssignmentStatement(AssignmentStatement statement)
		{
			Visit(statement.AssignmentTarget);
			Visit(statement.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="ReturnStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
		protected internal override void VisitReturnStatement(ReturnStatement statement)
		{
			Visit(statement.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="StateFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="StateFormula" /> instance that should be visited.</param>
		protected internal override void VisitStateFormula(StateFormula formula)
		{
			Visit(formula.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="BinaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="BinaryFormula" /> instance that should be visited.</param>
		protected internal override void VisitBinaryFormula(BinaryFormula formula)
		{
			Visit(formula.LeftOperand);
			Visit(formula.RightOperand);
		}

		/// <summary>
		///     Visits an element of type <see cref="UnaryFormula" />.
		/// </summary>
		/// <param name="formula">The <see cref="UnaryFormula" /> instance that should be visited.</param>
		protected internal override void VisitUnaryFormula(UnaryFormula formula)
		{
			Visit(formula.Operand);
		}
	}
}