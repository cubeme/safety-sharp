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

namespace SafetySharp.Runtime.BoundTree
{
	using System;
	using System.Globalization;

	/// <summary>
	///     Represents an enumeration literal expression.
	/// </summary>
	public sealed class EnumerationLiteralExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="value">The value that should be represented by the expression.</param>
		public EnumerationLiteralExpression(object value)
		{
			Value = value;
		}

		/// <summary>
		///     Gets the value represented by the expression.
		/// </summary>
		public object Value { get; private set; }

		/// <summary>
		///     Gets the value represented by the expression as an <see cref="int" />.
		/// </summary>
		public int IntegerValue
		{
			get { return ((IConvertible)Value).ToInt32(CultureInfo.InvariantCulture); }
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitEnumerationLiteralExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitEnumerationLiteralExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitEnumerationLiteralExpression" /> method on the
		///     <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitEnumerationLiteralExpression(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Expression expression)
		{
			var literalExpression = expression as EnumerationLiteralExpression;
			if (literalExpression == null)
				return false;

			return Value.Equals(literalExpression.Value);
		}
	}
}