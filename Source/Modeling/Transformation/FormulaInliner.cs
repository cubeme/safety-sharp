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
	using Runtime.BoundTree;
	using Runtime.Formulas;
	using Utilities;

	/// <summary>
	///     Inlines <see cref="MethodInvocationExpression" />s within <see cref="Formula" />s recursively. Checks that there are no
	///     cycles in the method call graph.
	/// </summary>
	internal class FormulaInliner : BoundTreeRewriter
	{
		/// <summary>
		///     Used to replace method argument variables with their actual expressions.
		/// </summary>
		private readonly VariableReplacer _variableReplacer = new VariableReplacer();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private FormulaInliner()
		{
		}

		/// <summary>
		///     Recursively inlines all methods invoked within the <paramref name="formula" />.
		/// </summary>
		/// <param name="formula">The formula which should have all invoked methods inlined.</param>
		public static Formula Inline(Formula formula)
		{
			Requires.NotNull(formula, () => formula);

			var inliner = new FormulaInliner();
			return (Formula)inliner.Visit(formula);
		}

		/// <summary>
		///     Visits an element of type <see cref="MethodInvocationExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="MethodInvocationExpression" /> instance that should be visited.</param>
		protected internal override BoundNode VisitMethodInvocationExpression(MethodInvocationExpression expression)
		{
			var body = expression.Method.MethodBody.Body;
			var returnStatement = body.Statements[0] as ReturnStatement;

			Requires.That(returnStatement != null,
				"Detected an invalid invocation of method '{0}' declared by '{1}' within the formula: The invoked method does not " +
				"consist of a single return statement only.",
				expression.Method.MethodInfo, expression.Method.MethodInfo.DeclaringType.FullName);

			_variableReplacer.AddArgumentReplacements(expression);

			var replacedBody = (Expression)_variableReplacer.Visit(returnStatement.Expression);
			return Visit(replacedBody);
		}
	}
}