﻿// The MIT License (MIT)
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

namespace SafetySharp.Runtime.MetadataAnalyzers
{
	using System;
	using Expressions;
	using Statements;
	using Utilities;

	/// <summary>
	///     Visits the <see cref="Statement" />s and <see cref="Expression" />s contained in the body of a S# method.
	/// </summary>
	public abstract class MethodBodyVisitor
	{
		/// <summary>
		///     Visits an element of type <see cref="ArgumentExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ArgumentExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitArgumentExpression(ArgumentExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="BinaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BinaryExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitBinaryExpression(BinaryExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="BooleanLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="BooleanLiteralExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitBooleanLiteralExpression(BooleanLiteralExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="ConditionalExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ConditionalExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitConditionalExpression(ConditionalExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="DoubleLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="DoubleLiteralExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitDoubleLiteralExpression(DoubleLiteralExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="EnumerationLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="EnumerationLiteralExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitEnumerationLiteralExpression(EnumerationLiteralExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="FieldExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="FieldExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitFieldExpression(FieldExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="MethodInvocationExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="MethodInvocationExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitMethodInvocationExpression(MethodInvocationExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="IntegerLiteralExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="IntegerLiteralExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitIntegerLiteralExpression(IntegerLiteralExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="UnaryExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="UnaryExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitUnaryExpression(UnaryExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="VariableExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="VariableExpression" /> instance that should be visited.</param>
		protected internal abstract void VisitVariableExpression(VariableExpression expression);

		/// <summary>
		///     Visits an element of type <see cref="BlockStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="BlockStatement" /> instance that should be visited.</param>
		protected internal abstract void VisitBlockStatement(BlockStatement statement);

		/// <summary>
		///     Visits an element of type <see cref="ChoiceStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ChoiceStatement" /> instance that should be visited.</param>
		protected internal abstract void VisitChoiceStatement(ChoiceStatement statement);

		/// <summary>
		///     Visits an element of type <see cref="ExpressionStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
		protected internal abstract void VisitExpressionStatement(ExpressionStatement statement);

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal abstract void VisitAssignmentStatement(AssignmentStatement statement);

		/// <summary>
		///     Visits an element of type <see cref="ReturnStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ReturnStatement" /> instance that should be visited.</param>
		protected internal abstract void VisitReturnStatement(ReturnStatement statement);

		/// <summary>
		///     Visits the <paramref name="statement" />.
		/// </summary>
		/// <param name="statement">The statement that should be visited.</param>
		public void Visit(Statement statement)
		{
			Requires.NotNull(statement, () => statement);
			statement.Accept(this);
		}

		/// <summary>
		///     Visits the <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression that should be visited.</param>
		public void Visit(Expression expression)
		{
			Requires.NotNull(expression, () => expression);
			expression.Accept(this);
		}
	}
}