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

namespace SafetySharp.Modeling
{
	using System;
	using System.Linq.Expressions;

	/// <summary>
	///     Provides factory methods for CTL operators.
	/// </summary>
	public class CtlOperatorFactory
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private CtlOperatorFactory()
		{
			throw new NotSupportedException();
		}

		#region Next

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public CtlFormula Next(CtlFormula operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public CtlFormula Next(Expression<Func<bool>> operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'next' operator should be applied to.</param>
		public CtlFormula Next([LiftExpression] bool operand)
		{
			throw new NotSupportedException();
		}

		#endregion

		#region Finally

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public CtlFormula Finally(CtlFormula operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'finally' operator should be applied to.</param>
		public CtlFormula Finally([LiftExpression] bool operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public CtlFormula Finally(Expression<Func<bool>> operand)
		{
			throw new NotSupportedException();
		}

		#endregion

		#region Globally

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public CtlFormula Globally(CtlFormula operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'globally' operator should be applied to.</param>
		public CtlFormula Globally([LiftExpression] bool operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public CtlFormula Globally(Expression<Func<bool>> operand)
		{
			throw new NotSupportedException();
		}

		#endregion

		#region Until

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until([LiftExpression] bool leftOperand, [LiftExpression] bool rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(Expression<Func<bool>> leftOperand, Expression<Func<bool>> rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(CtlFormula leftOperand, CtlFormula rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(Expression<Func<bool>> leftOperand, CtlFormula rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(CtlFormula leftOperand, Expression<Func<bool>> rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until([LiftExpression] bool leftOperand, CtlFormula rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(CtlFormula leftOperand, [LiftExpression] bool rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until([LiftExpression] bool leftOperand, Expression<Func<bool>> rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public CtlFormula Until(Expression<Func<bool>> leftOperand, [LiftExpression] bool rightOperand)
		{
			throw new NotSupportedException();
		}

		#endregion
	}
}