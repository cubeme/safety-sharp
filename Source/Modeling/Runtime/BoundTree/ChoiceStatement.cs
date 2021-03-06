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
	///     Represents a nondeterministic choice.
	/// </summary>
	public class ChoiceStatement : Statement
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="guards">The expressions representing the guards of the individual nondeterministic choices.</param>
		/// <param name="statements">The statements representing the actions of the individual nondeterministic choices.</param>
		/// <param name="isDeterministic">Indicates whether the choice is deterministic.</param>
		public ChoiceStatement(IReadOnlyList<Expression> guards, IReadOnlyList<Statement> statements, bool isDeterministic)
		{
			Requires.NotNull(guards, () => guards);
			Requires.NotNull(statements, () => statements);
			Requires.That(guards.Count() == statements.Count(), "The number of guards and bodies must match.");

			Guards = guards;
			Statements = statements;
			IsDeterministic = isDeterministic;
		}

		/// <summary>
		///     Gets the expressions representing the guards belonging to the <see cref="Statements" />.
		/// </summary>
		public IReadOnlyList<Expression> Guards { get; private set; }

		/// <summary>
		///     Gets the statements representing the actions belonging to the <see cref="Guards" />.
		/// </summary>
		public IReadOnlyList<Statement> Statements { get; private set; }

		/// <summary>
		///     Gets the number of choices.
		/// </summary>
		public int ChoiceCount
		{
			get { return Guards.Count; }
		}

		/// <summary>
		///     Gets a value indicating whether the choice is deterministic.
		/// </summary>
		public bool IsDeterministic { get; private set; }

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor.VisitChoiceStatement" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override void Accept(BoundTreeVisitor visitor)
		{
			visitor.VisitChoiceStatement(this);
		}

		/// <summary>
		///     Calls the <see cref="BoundTreeVisitor{TResult}.VisitChoiceStatement" /> method on the <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be accepted.</param>
		internal override TResult Accept<TResult>(BoundTreeVisitor<TResult> visitor)
		{
			return visitor.VisitChoiceStatement(this);
		}
	}
}