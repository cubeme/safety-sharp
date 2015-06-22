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

namespace SafetySharp.Runtime.Statements
{
	using System;
	using System.Collections.Generic;
	using Expressions;
	using MetadataAnalyzers;
	using Utilities;

	/// <summary>
	///     Represents the invocation of a S# method, optionally storing the method's return value in a variable,
	///     field, or method parameter.
	/// </summary>
	public sealed class MethodInvocationStatement : Statement
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="method">The metadata of the method that should be invoked by the expression.</param>
		/// <param name="arguments">The arguments the method should be invoked with.</param>
		/// <param name="returnValue">
		///     The expression representing the variable, field, or method parameter the method's return value should be stored in.
		///     Must be <c>null</c> if the method doesn't return a value; can be <c>null</c> if the method's return value should be
		///     discarded.
		/// </param>
		public MethodInvocationStatement(MethodMetadata method, IEnumerable<ArgumentExpression> arguments, Expression returnValue)
		{
			Requires.NotNull(method, () => method);
			Requires.NotNull(arguments, () => arguments);
			Requires.That(method.MethodInfo.ReturnType != typeof(void) || returnValue == null, "Cannot store result of void-returning method.");

			Arguments = arguments;
			ReturnValue = returnValue;
			Method = method;
		}

		/// <summary>
		///     Gets the arguments the method is invoked with.
		/// </summary>
		public IEnumerable<ArgumentExpression> Arguments { get; private set; }

		/// <summary>
		///     Gets the expression representing the variable, field, or method parameter the method's return value should is stored in.
		///     Returns <c>null</c> if the method's return value is discarded or the method doesn't return a value.
		/// </summary>
		public Expression ReturnValue { get; private set; }

		/// <summary>
		///     Gets the metadata of the method invoked by the expression.
		/// </summary>
		public MethodMetadata Method { get; private set; }

		/// <summary>
		///     Calls the <see cref="MethodBodyVisitor.VisitMethodInvocationStatement" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(MethodBodyVisitor visitor)
		{
			visitor.VisitMethodInvocationStatement(this);
		}
	}
}