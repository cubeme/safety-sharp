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

namespace SafetySharp.Analysis
{
	using System;
	using Runtime.Formulas;
	using Utilities;

	/// <summary>
	///     Represents a computation tree logic formula. Use the factory methods declared by the <see cref="Ctl" /> class to create
	///     a <see cref="CtlFormula" />.
	/// </summary>
	public class CtlFormula
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="formula">The formula that should be wrapped by this instance.</param>
		internal CtlFormula(Formula formula)
		{
			Requires.NotNull(formula, () => formula);
			Formula = formula;
		}

		/// <summary>
		///     Gets the <see cref="Formula" /> wrapped by this instance.
		/// </summary>
		internal Formula Formula { get; private set; }

		/// <summary>
		///     Converts the <paramref name="expression" /> to an instance of <see cref="CtlFormula" />.
		/// </summary>
		/// <param name="expression">The expression that should be converted.</param>
		public static implicit operator CtlFormula(bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the implication operator to this instance (the antecedent) and
		///     <paramref name="formula" /> (the succedent).
		/// </summary>
		/// <param name="formula">The formula representing the succedent of the implication.</param>
		public CtlFormula Implies(CtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new CtlFormula(new BinaryFormula(Formula, BinaryFormulaOperator.Implication, PathQuantifier.None, formula.Formula));
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the equivalence operator to this instance and
		///     <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula that should be equivalent.</param>
		public CtlFormula EquivalentTo(CtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new CtlFormula(new BinaryFormula(Formula, BinaryFormulaOperator.Equivalence, PathQuantifier.None, formula.Formula));
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'not' operator to the <paramref name="formula" />.
		/// </summary>
		public static CtlFormula operator !(CtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new CtlFormula(new UnaryFormula(formula.Formula, UnaryFormulaOperator.Not, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'conjunction' operator to <paramref name="left" /> and
		///     <paramref name="right" />.
		/// </summary>
		public static CtlFormula operator &(CtlFormula left, CtlFormula right)
		{
			Requires.NotNull(left, () => left);
			Requires.NotNull(right, () => right);

			return new CtlFormula(new BinaryFormula(left.Formula, BinaryFormulaOperator.And, PathQuantifier.None, right.Formula));
		}

		/// <summary>
		///     Returns a <see cref="CtlFormula" /> that applies the 'disjunction' operator to <paramref name="left" /> and
		///     <paramref name="right" />.
		/// </summary>
		public static CtlFormula operator |(CtlFormula left, CtlFormula right)
		{
			Requires.NotNull(left, () => left);
			Requires.NotNull(right, () => right);

			return new CtlFormula(new BinaryFormula(left.Formula, BinaryFormulaOperator.Or, PathQuantifier.None, right.Formula));
		}
	}
}