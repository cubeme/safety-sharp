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
	using Utilities;

	/// <summary>
	///     Represents the application of a <see cref="UnaryOperator" /> to an <see cref="Expression" /> operand.
	/// </summary>
	public sealed class UnaryExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="unaryOperator">The unary operator that should be applied to the <paramref name="operand" />.</param>
		/// <param name="operand">The operand the <paramref name="unaryOperator" /> should be applied to.</param>
		public UnaryExpression(UnaryOperator unaryOperator, Expression operand)
		{
			Requires.InRange(unaryOperator, () => unaryOperator);
			Requires.NotNull(operand, () => operand);

			Operand = operand;
			Operator = unaryOperator;
		}

		/// <summary>
		///     Gets the operand the <see cref="Operator" /> is applied to.
		/// </summary>
		public Expression Operand { get; private set; }

		/// <summary>
		///     Gets the unary operator that is applied to the <see cref="Operand" />.
		/// </summary>
		public UnaryOperator Operator { get; private set; }

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitUnaryExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitUnaryExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitUnaryExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitUnaryExpression(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Expression expression)
		{
			var unaryExpression = expression as UnaryExpression;
			if (unaryExpression == null)
				return false;

			return Operator == unaryExpression.Operator && Operand.IsStructurallyEquivalent(unaryExpression.Operand);
		}
	}
}