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

namespace SafetySharp.Runtime.BoundTree
{
	using System;
	using Utilities;

	/// <summary>
	///     Represents an assignment of an expression to a writable target expression.
	/// </summary>
	public sealed class AssignmentStatement : Statement
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="assignmentTarget">The writable target the <paramref name="expression" /> should be assigned to.</param>
		/// <param name="expression">
		///     The expression representing the value that should be assigned to the <paramref name="assignmentTarget" />.
		/// </param>
		public AssignmentStatement(Expression assignmentTarget, Expression expression)
		{
			Requires.NotNull(assignmentTarget, () => assignmentTarget);
			Requires.NotNull(expression, () => expression);

			AssignmentTarget = assignmentTarget;
			Expression = expression;
		}

		/// <summary>
		///     Gets the expression representing the value that is assigned to the <see cref="AssignmentTarget" />.
		/// </summary>
		public Expression Expression { get; private set; }

		/// <summary>
		///     Gets the writable <see cref="Expression" /> representing the target of the assignment.
		/// </summary>
		public Expression AssignmentTarget { get; private set; }

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitAssignmentStatement" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitAssignmentStatement(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitAssignmentStatement" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitAssignmentStatement(this);
		}
	}
}