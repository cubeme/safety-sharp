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
	using Analysis.Formulas;
	using Analysis.Transformation;
	using Utilities;

	/// <summary>
	///     Represents a conditional expression that selects between two branches at run-time.
	/// </summary>
	public sealed class ConditionalExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="condition">The condition that selects between the two branches.</param>
		/// <param name="trueBranch">The expression that is executed when the <paramref name="condition" /> holds.</param>
		/// <param name="falseBranch">The expression that is executed when the <paramref name="condition" /> does not hold.</param>
		public ConditionalExpression(Expression condition, Expression trueBranch, Expression falseBranch)
		{
			Requires.NotNull(condition, () => condition);
			Requires.NotNull(trueBranch, () => trueBranch);
			Requires.NotNull(falseBranch, () => falseBranch);

			Condition = condition;
			TrueBranch = trueBranch;
			FalseBranch = falseBranch;
		}

		/// <summary>
		///     Gets the condition that selects between the two branches.
		/// </summary>
		public Expression Condition { get; private set; }

		/// <summary>
		///     Gets the expression that is executed when the <see cref="Condition" /> holds.
		/// </summary>
		public Expression TrueBranch { get; private set; }

		/// <summary>
		///     Gets the expression that is executed when the <see cref="Condition" /> does not hold.
		/// </summary>
		public Expression FalseBranch { get; private set; }

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitConditionalExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitConditionalExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitConditionalExpression" /> method on the <paramref name="visitor" />
		///     .
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitConditionalExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="FormulaVisitor.VisitConditionalExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(FormulaVisitor visitor)
		{
			visitor.VisitConditionalExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="FormulaVisitor{TResult}.VisitConditionalExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(FormulaVisitor<TResult> visitor)
		{
			return visitor.VisitConditionalExpression(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Expression expression)
		{
			var conditionalExpression = expression as ConditionalExpression;
			if (conditionalExpression == null)
				return false;

			return Condition.IsStructurallyEquivalent(conditionalExpression.Condition) &&
				   TrueBranch.IsStructurallyEquivalent(conditionalExpression.TrueBranch) &&
				   FalseBranch.IsStructurallyEquivalent(conditionalExpression.FalseBranch);
		}
	}
}