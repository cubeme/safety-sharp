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

namespace SafetySharp.Analysis.Formulas
{
	using System;
	using Runtime;
	using Runtime.Expressions;
	using Utilities;

	/// <summary>
	///     Represents a state formula wrapping an <see cref="Expression" /> that is evaluated in a single system state.
	/// </summary>
	public sealed class StateFormula : Formula
	{
		/// <summary>
		///     The lazily evaluated <see cref="Expression" /> that represents the state formula.
		/// </summary>
		private readonly Lazy<Expression> _expression;

		/// <summary>
		///     Initializes a new instance of the <see cref="StateFormula" /> class.
		/// </summary>
		/// <param name="expression">The lazily evaluated metamodel expression that represents the state formula.</param>
		internal StateFormula(Lazy<Expression> expression)
		{
			Requires.NotNull(expression, () => expression);
			_expression = expression;
		}

		/// <summary>
		///     Initializes a new instance of the <see cref="StateFormula" /> class.
		/// </summary>
		/// <param name="expression">The metamodel expression that represents the state formula.</param>
		/// <remarks>For testing purposes.</remarks>
		internal StateFormula(Expression expression)
		{
			Requires.NotNull(expression, () => expression);
			_expression = new Lazy<Expression>(() => expression);
		}

		/// <summary>
		///     Gets the <see cref="Expression" /> that represents the state formula.
		/// </summary>
		public Expression Expression
		{
			get { return _expression.Value; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula contains any temporal operators.
		/// </summary>
		public override bool IsTemporal
		{
			get { return false; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid linear temporal logic formula.
		/// </summary>
		public override bool IsLinearFormula
		{
			get { return true; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid computation tree logic formula.
		/// </summary>
		public override bool IsTreeFormula
		{
			get { return true; }
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="FormulaVisitor.VisitStateFormula(StateFormula)" /> method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override void Accept(FormulaVisitor visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			visitor.VisitStateFormula(this);
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="FormulaVisitor{TResult}.VisitStateFormula(StateFormula)" /> method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override TResult Accept<TResult>(FormulaVisitor<TResult> visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			return visitor.VisitStateFormula(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Formula formula)
		{
			var stateFormula = formula as StateFormula;
			if (stateFormula == null)
				return false;

			return Expression.IsStructurallyEquivalent(stateFormula.Expression);
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			var serializer = new CSharpSerializer();
			return serializer.Serialize(Expression);
		}
	}
}