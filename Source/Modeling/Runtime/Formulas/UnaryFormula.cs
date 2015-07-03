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

namespace SafetySharp.Runtime.Formulas
{
	using System;
	using BoundTree;
	using Utilities;

	/// <summary>
	///     Represents the application of a <see cref="UnaryFormulaOperator" /> to a <see cref="Formula" /> instance.
	/// </summary>
	public sealed class UnaryFormula : Formula
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="UnaryFormula" /> class.
		/// </summary>
		/// <param name="operand">The operand of the unary formula.</param>
		/// <param name="unaryOperator">The operator of the unary formula.</param>
		/// <param name="pathQuantifier">The path quantifier of the unary formula.</param>
		internal UnaryFormula(Formula operand, UnaryFormulaOperator unaryOperator, PathQuantifier pathQuantifier)
		{
			Requires.NotNull(operand, () => operand);
			Requires.InRange(unaryOperator, () => unaryOperator);
			Requires.InRange(pathQuantifier, () => pathQuantifier);

			Operand = operand;
			Operator = unaryOperator;
			PathQuantifier = pathQuantifier;
		}

		/// <summary>
		///     Gets the operand of the unary formula.
		/// </summary>
		public Formula Operand { get; private set; }

		/// <summary>
		///     Gets the operator of the unary formula.
		/// </summary>
		public UnaryFormulaOperator Operator { get; private set; }

		/// <summary>
		///     Gets the path quantifier of the unary formula.
		/// </summary>
		public PathQuantifier PathQuantifier { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the formula contains any temporal operators.
		/// </summary>
		public override bool IsTemporal
		{
			get
			{
				switch (Operator)
				{
					case UnaryFormulaOperator.Next:
					case UnaryFormulaOperator.Finally:
					case UnaryFormulaOperator.Globally:
						return true;
					case UnaryFormulaOperator.Not:
						return Operand.IsTemporal;
					default:
						Assert.NotReached("Unknown unary temporal operator.");
						return false;
				}
			}
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid linear temporal logic formula.
		/// </summary>
		public override bool IsLinearFormula
		{
			get { return PathQuantifier == PathQuantifier.None && Operand.IsLinearFormula; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid computation tree logic formula.
		/// </summary>
		public override bool IsTreeFormula
		{
			get { return (!IsTemporal || PathQuantifier != PathQuantifier.None) && Operand.IsTreeFormula; }
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="FormulaVisitor.VisitUnaryFormula(UnaryFormula)" /> method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			visitor.VisitUnaryFormula(this);
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="BoundTreeVisitor{TResult}.VisitUnaryFormula(UnaryFormula)" /> method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			return visitor.VisitUnaryFormula(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Formula formula)
		{
			var unaryFormula = formula as UnaryFormula;
			if (unaryFormula == null)
				return false;

			return Operator == unaryFormula.Operator &&
				   PathQuantifier == unaryFormula.PathQuantifier &&
				   Operand.IsStructurallyEquivalent(unaryFormula.Operand);
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			var operatorSymbol = "";

			switch (PathQuantifier)
			{
				case PathQuantifier.All:
					operatorSymbol = "A";
					break;
				case PathQuantifier.Exists:
					operatorSymbol = "E";
					break;
				case PathQuantifier.None:
					break;
				default:
					Assert.NotReached("Unknown path quantifier.");
					break;
			}

			switch (Operator)
			{
				case UnaryFormulaOperator.Next:
					operatorSymbol += "X";
					break;
				case UnaryFormulaOperator.Finally:
					operatorSymbol += "F";
					break;
				case UnaryFormulaOperator.Globally:
					operatorSymbol += "G";
					break;
				case UnaryFormulaOperator.Not:
					operatorSymbol = "!";
					break;
				default:
					Assert.NotReached("Unknown unary temporal operator.");
					break;
			}

			return String.Format("({0} {1})", operatorSymbol, Operand);
		}
	}
}