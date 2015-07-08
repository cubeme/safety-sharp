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
	///     Represents a state formula wrapping an <see cref="Expression" /> that is evaluated in a single system state.
	/// </summary>
	public sealed class FaultOccurrenceFormula : Formula
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="StateFormula" /> class.
		/// </summary>
		/// <param name="fault">The fault whose occurrence should be checked by the formula.</param>
		internal FaultOccurrenceFormula(FaultMetadata fault)
		{
			Requires.NotNull(fault, () => fault);
			Fault = fault;
		}

		/// <summary>
		///     Gets the fault whose occurrence is checked by the formula.
		/// </summary>
		public FaultMetadata Fault { get; private set; }

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
		///     <see cref="BoundTreeVisitor.VisitFaultOccurrenceFormula(FaultOccurrenceFormula)" /> method.
		/// </summary>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			visitor.VisitFaultOccurrenceFormula(this);
		}

		/// <summary>
		///     Implements the visitor pattern, calling <paramref name="visitor" />'s
		///     <see cref="BoundTreeVisitor{TResult}.VisitFaultOccurrenceFormula(FaultOccurrenceFormula)" /> method.
		/// </summary>
		/// <typeparam name="TResult">The type of the value returned by <paramref name="visitor" />.</typeparam>
		/// <param name="visitor">The visitor the type-specific visit method should be invoked on.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			Requires.NotNull(visitor, () => visitor);
			return visitor.VisitFaultOccurrenceFormula(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Formula formula)
		{
			var faultOccurrenceFormula = formula as FaultOccurrenceFormula;
			if (faultOccurrenceFormula == null)
				return false;

			return Fault == faultOccurrenceFormula.Fault;
		}

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("IsOcurring<{0}>({1})", Fault.Fault.GetType().FullName, Fault.DeclaringComponent.Name);
		}
	}
}