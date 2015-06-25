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
	///     Represents a linear temporal logic formula. Use the factory methods declared by the <see cref="Ltl" /> class to create
	///     a <see cref="LtlFormula" />.
	/// </summary>
	public class LtlFormula
	{
		/// <summary>
		///     The actual <see cref="Formula" /> wrapped by this instance.
		/// </summary>
		private Formula _formula;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private LtlFormula()
		{
		}

		/// <summary>
		///     Converts the <paramref name="formula" /> to an instance of <see cref="Formula" />.
		/// </summary>
		/// <param name="formula">The formula that should be converted.</param>
		public static implicit operator Formula(LtlFormula formula)
		{
			return formula._formula;
		}

		/// <summary>
		///     Converts the <paramref name="formula" /> to an instance of <see cref="LtlFormula" />.
		/// </summary>
		/// <param name="formula">The formula that should be converted.</param>
		public static implicit operator LtlFormula(Formula formula)
		{
			return new LtlFormula { _formula = formula };
		}

		#region Formula

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the implication operator to this instance (the antecedent) and
		///     <paramref name="formula" /> (the succedent).
		/// </summary>
		/// <param name="formula">The formula representing the succedent of the implication.</param>
		public LtlFormula Implies(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new BinaryFormula(_formula, BinaryFormulaOperator.Implication, PathQuantifier.None, formula);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the equivalence operator to this instance and
		///     <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula that should be equivalent.</param>
		public LtlFormula EquivalentTo(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new BinaryFormula(_formula, BinaryFormulaOperator.Equivalence, PathQuantifier.None, formula);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'conjunction' operator to this instance and
		///     <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The second operand of the conjunction.</param>
		public LtlFormula And(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new BinaryFormula(_formula, BinaryFormulaOperator.And, PathQuantifier.None, formula);
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'disjunction' operator to this instance and
		///     <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The second operator of the disjunction.</param>
		public LtlFormula Or(LtlFormula formula)
		{
			Requires.NotNull(formula, () => formula);
			return new BinaryFormula(_formula, BinaryFormulaOperator.Or, PathQuantifier.None, formula);
		}

		#endregion

		#region Expression

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the implication operator to this instance (the antecedent) and
		///     <paramref name="expression" /> (the succedent).
		/// </summary>
		/// <param name="expression">The formula representing the succedent of the implication.</param>
		public LtlFormula Implies(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return Implies(CSharpTransformation.Transform(expression));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the equivalence operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The formula that should be equivalent.</param>
		public LtlFormula EquivalentTo(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return EquivalentTo(CSharpTransformation.Transform(expression));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'conjunction' operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The second operand of the conjunction.</param>
		public LtlFormula And(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return And(CSharpTransformation.Transform(expression));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'disjunction' operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The second operator of the disjunction.</param>
		public LtlFormula Or(Expression<Func<bool>> expression)
		{
			Requires.NotNull(expression, () => expression);
			return Or(CSharpTransformation.Transform(expression));
		}

		#endregion

		#region Unlifted

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the implication operator to this instance (the antecedent) and
		///     <paramref name="expression" /> (the succedent).
		/// </summary>
		/// <param name="expression">[LiftExpression] The formula representing the succedent of the implication.</param>
		public LtlFormula Implies([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the equivalence operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">[LiftExpression] The formula that should be equivalent.</param>
		public LtlFormula EquivalentTo([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'conjunction' operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">[LiftExpression] The second operand of the conjunction.</param>
		public LtlFormula And([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'disjunction' operator to this instance and
		///     <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">[LiftExpression] The second operator of the disjunction.</param>
		public LtlFormula Or([LiftExpression] bool expression)
		{
			Requires.CompilationTransformation();
			return null;
		}

		#endregion
	}
}