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
	using System.Collections.Immutable;
	using Formulas;
	using Utilities;

	/// <summary>
	///     Provides factory methods for the construction of linear temporal logic formulas.
	/// </summary>
	public static class Ltl
	{
		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static LtlFormula Next(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryTemporalOperator.Next, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula Finally(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryTemporalOperator.Finally, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula Globally(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryTemporalOperator.Globally, PathQuantifier.None));
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

			return new LtlFormula(new BinaryFormula(leftOperand.Formula, BinaryTemporalOperator.Until, PathQuantifier.None, rightOperand.Formula));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that represents the C# <paramref name="expression" />. All non-literal values
		///     accessed
		///     by <paramref name="expression" /> must be passed in the <paramref name="values" /> array, with the
		///     <paramref name="expression" /> referencing the objects in a <see cref="String.Format(string, object[])" /> like fashion.
		/// </summary>
		/// <param name="expression">The C# expression representing the state formula.</param>
		/// <param name="values">The non-literal values referenced by <paramref name="expression" />.</param>
		public static LtlFormula StateFormula(string expression, params object[] values)
		{
			Requires.NotNullOrWhitespace(expression, () => expression);
			return new LtlFormula(new UntransformedStateFormula(expression, values.ToImmutableArray()));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static LtlFormula Next([StateFormula] bool operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula Finally([StateFormula] bool operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula Globally([StateFormula] bool operand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until([StateFormula] bool leftOperand, LtlFormula rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until(LtlFormula leftOperand, [StateFormula] bool rightOperand)
		{
			throw new NotSupportedException();
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula Until([StateFormula] bool leftOperand, [StateFormula] bool rightOperand)
		{
			throw new NotSupportedException();
		}
	}
}