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
	using Utilities;

	/// <summary>
	///     Represents the application of a <see cref="BinaryFormulaOperator" /> to two <see cref="Formula" /> instances.
	/// </summary>
	public sealed class BinaryFormula : Formula
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="BinaryFormula" /> class.
		/// </summary>
		/// <param name="leftOperand">The formula on the left-hand side of the binary operator.</param>
		/// <param name="binaryOperator">The operator of the binary formula.</param>
		/// <param name="pathQuantifier">The path quantifier of the binary formula.</param>
		/// <param name="rightOperand">The formula on the right-hand side of the binary operator.</param>
		internal BinaryFormula(Formula leftOperand, BinaryFormulaOperator binaryOperator, PathQuantifier pathQuantifier, Formula rightOperand)
		{
			Requires.NotNull(leftOperand, () => leftOperand);
			Requires.InRange(binaryOperator, () => binaryOperator);
			Requires.InRange(pathQuantifier, () => pathQuantifier);
			Requires.NotNull(rightOperand, () => rightOperand);

			LeftOperand = leftOperand;
			Operator = binaryOperator;
			PathQuantifier = pathQuantifier;
			RightOperand = rightOperand;
		}

		/// <summary>
		///     Gets the formula on the left-hand side of the binary operator.
		/// </summary>
		public Formula LeftOperand { get; private set; }

		/// <summary>
		///     Gets the operator of the binary formula.
		/// </summary>
		public BinaryFormulaOperator Operator { get; private set; }

		/// <summary>
		///     Gets the path quantifier of the binary formula.
		/// </summary>
		public PathQuantifier PathQuantifier { get; private set; }

		/// <summary>
		///     Gets the formula on the right-hand side of the binary operator.
		/// </summary>
		public Formula RightOperand { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the formula contains any temporal operators.
		/// </summary>
		public override bool IsTemporal
		{
			get
			{
				switch (Operator)
				{
					case BinaryFormulaOperator.And:
					case BinaryFormulaOperator.Or:
					case BinaryFormulaOperator.Implication:
					case BinaryFormulaOperator.Equivalence:
						return LeftOperand.IsTemporal || RightOperand.IsTemporal;
					case BinaryFormulaOperator.Until:
						return true;
					default:
						Assert.NotReached("Unknown binary temporal operator.");
						return false;
				}
			}
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid linear temporal logic formula.
		/// </summary>
		public override bool IsLinearFormula
		{
			get { return PathQuantifier == PathQuantifier.None && LeftOperand.IsLinearFormula && RightOperand.IsLinearFormula; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid computation tree logic formula.
		/// </summary>
		public override bool IsTreeFormula
		{
			get { return (!IsTemporal || PathQuantifier != PathQuantifier.None) && LeftOperand.IsTreeFormula && RightOperand.IsTreeFormula; }
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Formula formula)
		{
			var binaryFormula = formula as BinaryFormula;
			if (binaryFormula == null)
				return false;

			return PathQuantifier == binaryFormula.PathQuantifier &&
				   Operator == binaryFormula.Operator &&
				   LeftOperand.IsStructurallyEquivalent(binaryFormula.LeftOperand) &&
				   RightOperand.IsStructurallyEquivalent(binaryFormula.RightOperand);
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="FormulaVisitor.VisitBinaryFormula(BinaryFormula)" /> method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override void Accept(FormulaVisitor visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			visitor.VisitBinaryFormula(this);
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="FormulaVisitor{TResult}.VisitBinaryFormula(BinaryFormula)" /> method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override TResult Accept<TResult>(FormulaVisitor<TResult> visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			return visitor.VisitBinaryFormula(this);
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			var operatorSymbol = "";
			switch (Operator)
			{
				case BinaryFormulaOperator.And:
					operatorSymbol = "&&";
					break;
				case BinaryFormulaOperator.Or:
					operatorSymbol = "||";
					break;
				case BinaryFormulaOperator.Implication:
					operatorSymbol = "=>";
					break;
				case BinaryFormulaOperator.Equivalence:
					operatorSymbol = "<=>";
					break;
				case BinaryFormulaOperator.Until:
					switch (PathQuantifier)
					{
						case PathQuantifier.All:
							operatorSymbol = "AU";
							break;
						case PathQuantifier.Exists:
							operatorSymbol = "EU";
							break;
						case PathQuantifier.None:
							operatorSymbol = "U";
							break;
						default:
							Assert.NotReached("Unknown path quantifier.");
							break;
					}
					break;
				default:
					Assert.NotReached("Unknown binary temporal operator.");
					break;
			}

			return String.Format("({0} {1} {2})", LeftOperand, operatorSymbol, RightOperand);
		}
	}
}