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

namespace SafetySharp.Formulas
{
	using System;
	using Utilities;

	partial class BinaryFormula
	{
		/// <summary>
		///     Gets a value indicating whether the formula contains any temporal operators.
		/// </summary>
		public override bool IsTemporal
		{
			get
			{
				switch (Operator)
				{
					case BinaryTemporalOperator.And:
					case BinaryTemporalOperator.Or:
					case BinaryTemporalOperator.Implication:
					case BinaryTemporalOperator.Equivalence:
						return Left.IsTemporal || Right.IsTemporal;
					case BinaryTemporalOperator.Until:
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
			get { return PathQuantifier == PathQuantifier.None && Left.IsLinearFormula && Right.IsLinearFormula; }
		}

		/// <summary>
		///     Gets a value indicating whether the formula is a valid computation tree logic formula.
		/// </summary>
		public override bool IsTreeFormula
		{
			get { return (!IsTemporal || PathQuantifier != PathQuantifier.None) && Left.IsTreeFormula && Right.IsTreeFormula; }
		}

		/// <summary>
		///     Validates all of the property values.
		/// </summary>
		partial void Validate()
		{
			Assert.That(IsTemporal || PathQuantifier == PathQuantifier.None,
						"The path quantifier must be '{0}' for non-temporal operator '{1}'.", PathQuantifier.None, Operator);
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			var operatorSymbol = "";
			switch (Operator)
			{
				case BinaryTemporalOperator.And:
					operatorSymbol = "&&";
					break;
				case BinaryTemporalOperator.Or:
					operatorSymbol = "||";
					break;
				case BinaryTemporalOperator.Implication:
					operatorSymbol = "=>";
					break;
				case BinaryTemporalOperator.Equivalence:
					operatorSymbol = "<=>";
					break;
				case BinaryTemporalOperator.Until:
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

			return String.Format("({0} {1} {2})", Left, operatorSymbol, Right);
		}
	}
}