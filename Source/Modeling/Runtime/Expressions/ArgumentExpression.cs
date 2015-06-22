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

namespace SafetySharp.Runtime.Expressions
{
	using System;
	using MetadataAnalyzers;
	using Utilities;

	/// <summary>
	///     Represents an expression that is used to pass an argument to a method.
	/// </summary>
	public sealed class ArgumentExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="expression">The expression that should be passed to the method.</param>
		/// <param name="refKind">
		///     The reference kind of the argument, i.e., indicates whether the corresponding method parameter is declared as a
		///     <c>ref</c>, <c>out</c>, or neither of which.
		/// </param>
		public ArgumentExpression(Expression expression, RefKind refKind)
		{
			Requires.NotNull(expression, () => expression);
			Requires.InRange(refKind, () => refKind);

			Expression = expression;
			RefKind = refKind;
		}

		/// <summary>
		///     Gets the expression that should be passed to the method.
		/// </summary>
		public Expression Expression { get; private set; }

		/// <summary>
		///     Gets the reference kind of the argument, i.e., indicates whether the corresponding method parameter is declared as a
		///     <c>ref</c>, <c>out</c>, or neither of which.
		/// </summary>
		public RefKind RefKind { get; private set; }

		/// <summary>
		///     Calls the <see cref="MethodBodyVisitor.VisitArgumentExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(MethodBodyVisitor visitor)
		{
			visitor.VisitArgumentExpression(this);
		}
	}
}