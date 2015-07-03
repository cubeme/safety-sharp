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

namespace SafetySharp.Runtime.Expressions
{
	using System;
	using Analysis.Formulas;
	using MetadataAnalyzers;
	using Utilities;

	/// <summary>
	///     Represents the application of a <see cref="BinaryOperator" /> to two <see cref="Expression" /> operands.
	/// </summary>
	public sealed class BinaryExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="binaryOperator">
		///     The binary operator that should be applied to <paramref name="leftOperand" /> and <paramref name="rightOperand" />.
		/// </param>
		/// <param name="leftOperand">The left-hand operand the <paramref name="binaryOperator" /> should be applied to.</param>
		/// <param name="rightOperand">The right-hand operand the <paramref name="binaryOperator" /> should be applied to.</param>
		public BinaryExpression(BinaryOperator binaryOperator, Expression leftOperand, Expression rightOperand)
		{
			Requires.InRange(binaryOperator, () => binaryOperator);
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			LeftOperand = leftOperand;
			RightOperand = rightOperand;
			Operator = binaryOperator;
		}

		/// <summary>
		///     Gets the left-hand operand the <see cref="Operator" /> is applied to.
		/// </summary>
		public Expression LeftOperand { get; private set; }

		/// <summary>
		///     Gets the right-hand operand the <see cref="Operator" /> is applied to.
		/// </summary>
		public Expression RightOperand { get; private set; }

		/// <summary>
		///     Gets the binary operator that is applied to <see cref="LeftOperand" /> and <see cref="RightOperand" />.
		/// </summary>
		public BinaryOperator Operator { get; private set; }

		/// <summary>
		///     Calls the <see cref="MethodBodyVisitor.VisitBinaryExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(MethodBodyVisitor visitor)
		{
			visitor.VisitBinaryExpression(this);
		}
		/// <summary>
		///     Calls the <see cref="MethodBodyVisitor.VisitBinaryExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(FormulaVisitor visitor)
		{
			visitor.VisitBinaryExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="MethodBodyVisitor.VisitBinaryExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(FormulaVisitor<TResult> visitor)
		{
			return visitor.VisitBinaryExpression(this);
		}
		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Expression expression)
		{
			var binaryExpression = expression as BinaryExpression;
			if (binaryExpression == null)
				return false;

			return Operator == binaryExpression.Operator &&
				   LeftOperand.IsStructurallyEquivalent(binaryExpression.LeftOperand) &&
				   RightOperand.IsStructurallyEquivalent(binaryExpression.RightOperand);
		}
	}
}