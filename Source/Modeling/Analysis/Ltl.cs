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

namespace SafetySharp.Analysis
{
	using System;
	using System.Linq.Expressions;
	using CompilerServices;
	using Formulas;
	using Utilities;

	/// <summary>
	///     Provides factory methods for the construction of linear temporal logic formulas.
	/// </summary>
	public static class Ltl
	{
		#region StateExpression

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">[LiftExpression] The expression that should be evaluated.</param>
		public static LtlFormula StateExpression([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that evaluates <paramref name="expression" /> within a system state.
		/// </summary>
		/// <param name="expression">The expression that should be evaluated.</param>
		public static LtlFormula StateExpression(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return CSharpTransformation.Transform(expression);
		}

		#endregion

		#region Not

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'not' operator should be applied to.</param>
		public static LtlFormula Not(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Not, PathQuantifier.None);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'not' operator should be applied to.</param>
		public static LtlFormula Not(Expression<Func<bool>> operand)
		{
			Requires.NotNull(operand, () => operand);
			return Not(CSharpTransformation.Transform(operand));
		}

		#endregion

		#region Next

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static LtlFormula Next(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Next, PathQuantifier.None);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static LtlFormula Next(Expression<Func<bool>> operand)
		{
			Requires.NotNull(operand, () => operand);
			return Next(CSharpTransformation.Transform(operand));
		}

		#endregion

		#region Finally

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula Finally(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Finally, PathQuantifier.None);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula Finally(Expression<Func<bool>> operand)
		{
			Requires.NotNull(operand, () => operand);
			return Finally(CSharpTransformation.Transform(operand));
		}

		#endregion

		#region Globally

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula Globally(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Globally, PathQuantifier.None);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula Globally(Expression<Func<bool>> operand)
		{
			Requires.NotNull(operand, () => operand);
			return Globally(CSharpTransformation.Transform(operand));
		}

		#endregion

		#region Until

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(Expression<Func<bool>> leftOperand, Expression<Func<bool>> rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return Until(CSharpTransformation.Transform(leftOperand), CSharpTransformation.Transform(rightOperand));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(LtlFormula leftOperand, LtlFormula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return new BinaryFormula(leftOperand, BinaryFormulaOperator.Until, PathQuantifier.None, rightOperand);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(Expression<Func<bool>> leftOperand, LtlFormula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return Until(CSharpTransformation.Transform(leftOperand), rightOperand);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(LtlFormula leftOperand, Expression<Func<bool>> rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return Until(leftOperand, CSharpTransformation.Transform(rightOperand));
		}

		#endregion

		#region Unlifted

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'not' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'not' operator should be applied to.</param>
		public static LtlFormula Not([LiftExpression] bool operand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'next' operator should be applied to.</param>
		public static LtlFormula Next([LiftExpression] bool operand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula Finally([LiftExpression] bool operand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">[LiftExpression] The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula Globally([LiftExpression] bool operand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until([LiftExpression] bool leftOperand, [LiftExpression] bool rightOperand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until([LiftExpression] bool leftOperand, LtlFormula rightOperand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">[LiftExpression] The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until([LiftExpression] bool leftOperand, Expression<Func<bool>> rightOperand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(Expression<Func<bool>> leftOperand, [LiftExpression] bool rightOperand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">[LiftExpression] The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(LtlFormula leftOperand, [LiftExpression] bool rightOperand)
		{
			Requires.CompilationTransformation();
			return null;
		}

		#endregion
	}
}