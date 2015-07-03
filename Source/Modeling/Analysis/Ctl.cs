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
	using Runtime.Formulas;
	using Utilities;

	/// <summary>
	///     Provides factory methods for the construction of computation tree logic formulas.
	/// </summary>
	// ReSharper disable InconsistentNaming
	public static class Ctl
	{
		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" /> for all paths.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static CtlFormula AX(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Next, PathQuantifier.All);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'next' operator to <paramref name="operand" /> for any path.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static CtlFormula EX(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Next, PathQuantifier.Exists);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" /> for all paths.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static CtlFormula AF(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Finally, PathQuantifier.All);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'finally' operator to <paramref name="operand" /> for any path.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static CtlFormula EF(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Finally, PathQuantifier.Exists);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" /> for all paths.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static CtlFormula AG(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Globally, PathQuantifier.All);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'globally' operator to <paramref name="operand" /> for any path.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static CtlFormula EG(CtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new UnaryFormula(operand, UnaryFormulaOperator.Globally, PathQuantifier.Exists);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" /> for all paths.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static CtlFormula AU(CtlFormula leftOperand, CtlFormula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return new BinaryFormula(leftOperand, BinaryFormulaOperator.Until, PathQuantifier.All, rightOperand);
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" /> for any path.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static CtlFormula EU(CtlFormula leftOperand, CtlFormula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return new BinaryFormula(leftOperand, BinaryFormulaOperator.Until, PathQuantifier.Exists, rightOperand);
		}
	}
}