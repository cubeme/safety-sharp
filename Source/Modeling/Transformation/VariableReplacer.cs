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

namespace SafetySharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using Runtime;
	using Runtime.BoundTree;
	using Utilities;

	/// <summary>
	///     Replaces variables within a tree of <see cref="BoundNode" />s.
	/// </summary>
	internal class VariableReplacer : BoundTreeRewriter
	{
		/// <summary>
		///     Maps the variables that should be replaced to their replacement expressions.
		/// </summary>
		private readonly Dictionary<VariableMetadata, Expression> _replacedVariables = new Dictionary<VariableMetadata, Expression>();

		/// <summary>
		///     Adds the replacement <paramref name="expression" /> for the <paramref name="variable" />, causing the
		///     <paramref name="variable" /> to be replaced by <paramref name="expression" /> in all future replacement operations.
		/// </summary>
		/// <param name="variable">The variable that should be replaced by <paramref name="expression" />.</param>
		/// <param name="expression">The expression that <paramref name="variable" /> should be replaced with.</param>
		public void AddReplacedVariable(VariableMetadata variable, Expression expression)
		{
			Requires.NotNull(variable, () => variable);
			Requires.NotNull(expression, () => expression);
			Requires.That(!_replacedVariables.ContainsKey(variable), () => variable, "The variable has already been added.");

			_replacedVariables.Add(variable, expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="VariableExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="VariableExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitVariableExpression(VariableExpression expression)
		{
			Expression replacement;

			if (_replacedVariables.TryGetValue(expression.Variable, out replacement))
				return replacement;

			return expression;
		}
	}
}