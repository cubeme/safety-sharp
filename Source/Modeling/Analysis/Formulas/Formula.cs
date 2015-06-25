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

namespace SafetySharp.Analysis.Formulas
{
	using System;

	/// <summary>
	///     Represents a linear temporal logic or computation tree logic formula that can be modelchecked.
	/// </summary>
	public abstract class Formula
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		internal Formula()
		{
		}

		/// <summary>
		///     Gets a value indicating whether the formula contains any temporal operators.
		/// </summary>
		public abstract bool IsTemporal { get; }

		/// <summary>
		///     Gets a value indicating whether the formula is a valid linear temporal logic formula.
		/// </summary>
		public abstract bool IsLinearFormula { get; }

		/// <summary>
		///     Gets a value indicating whether the formula is a valid computation tree logic formula.
		/// </summary>
		public abstract bool IsTreeFormula { get; }

		/// <summary>
		///     Accepts <paramref name="visitor" />, calling the type-specific visit method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal abstract void Accept(FormulaVisitor visitor);

		/// <summary>
		///     Accepts <paramref name="visitor" />, calling the type-specific visit method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal abstract TResult Accept<TResult>(FormulaVisitor<TResult> visitor);

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula this instance should be structurally equivalent to.</param>
		internal abstract bool IsStructurallyEquivalent(Formula formula);
	}
}