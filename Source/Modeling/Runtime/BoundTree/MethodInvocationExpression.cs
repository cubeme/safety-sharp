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
	using System.Collections.Generic;
	using System.Linq;
	using Utilities;

	/// <summary>
	///     Represents an invocation of a S# method.
	/// </summary>
	public sealed class MethodInvocationExpression : Expression
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="method">The metadata of the method that should be invoked by the expression.</param>
		/// <param name="arguments">The arguments the method should be invoked with.</param>
		public MethodInvocationExpression(MethodMetadata method, params ArgumentExpression[] arguments)
		{
			Requires.NotNull(method, () => method);
			Requires.NotNull(arguments, () => arguments);

			Arguments = arguments;
			Method = method;
		}

		/// <summary>
		///     Gets the arguments the method is invoked with.
		/// </summary>
		public IEnumerable<ArgumentExpression> Arguments { get; private set; }

		/// <summary>
		///     Gets the metadata of the method invoked by the expression.
		/// </summary>
		public MethodMetadata Method { get; private set; }

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitMethodInvocationExpression" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitMethodInvocationExpression(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitMethodInvocationExpression" /> method on the
		///     <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitMethodInvocationExpression(this);
		}

		/// <summary>
		///     Gets a value indicating whether this instance is structurally equivalent to <paramref name="expression" />.
		/// </summary>
		/// <param name="expression">The expression this instance should be structurally equivalent to.</param>
		internal override bool IsStructurallyEquivalent(Expression expression)
		{
			var invocationExpression = expression as MethodInvocationExpression;
			if (invocationExpression == null)
				return false;

			if (Method != invocationExpression.Method)
				return false;

			var arguments = Arguments.ToArray();
			var otherArguments = invocationExpression.Arguments.ToArray();

			if (arguments.Length != otherArguments.Length)
				return false;

			return !arguments.Where((t, i) => !t.IsStructurallyEquivalent(otherArguments[i])).Any();
		}
	}
}