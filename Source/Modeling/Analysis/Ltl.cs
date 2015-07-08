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
	using Modeling;
	using Modeling.Faults;
	using Runtime;
	using Runtime.Formulas;
	using Utilities;

	/// <summary>
	///     Provides factory methods for the construction of linear temporal logic formulas.
	/// </summary>
	public static class Ltl
	{
		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that checks whether the fault of type <typeparamref name="TFault" /> is occurring
		///     for the <paramref name="component" />.
		/// </summary>
		/// <typeparam name="TFault">The type of the fault that should be occurring.</typeparam>
		/// <param name="component">The component the fault occurrence should be checked for.</param>
		public static LtlFormula IsOccurring<TFault>(IComponent component)
			where TFault : Fault
		{
			Requires.NotNull(component, () => component);
			return new LtlFormula(new FaultOccurrenceFormula(component.GetMetadata().GetFault<TFault>()));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'next' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'next' operator should be applied to.</param>
		public static LtlFormula X(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryFormulaOperator.Next, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'finally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'finally' operator should be applied to.</param>
		public static LtlFormula F(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryFormulaOperator.Finally, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'globally' operator to <paramref name="operand" />.
		/// </summary>
		/// <param name="operand">The operand the 'globally' operator should be applied to.</param>
		public static LtlFormula G(LtlFormula operand)
		{
			Requires.NotNull(operand, () => operand);
			return new LtlFormula(new UnaryFormula(operand.Formula, UnaryFormulaOperator.Globally, PathQuantifier.None));
		}

		/// <summary>
		///     Returns a <see cref="LtlFormula" /> that applies the 'until' operator to <paramref name="leftOperand" /> and
		///     <paramref name="rightOperand" />.
		/// </summary>
		/// <param name="leftOperand">The operand on the left-hand side of the 'until' operator.</param>
		/// <param name="rightOperand">The operand on the right-hand side of the 'until' operator.</param>
		public static LtlFormula U(LtlFormula leftOperand, LtlFormula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.NotNull(rightOperand, () => rightOperand);

			return new LtlFormula(new BinaryFormula(leftOperand.Formula, BinaryFormulaOperator.Until, PathQuantifier.None, rightOperand.Formula));
		}
	}
}