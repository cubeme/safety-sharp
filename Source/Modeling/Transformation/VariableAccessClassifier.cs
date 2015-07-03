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
	using Runtime;
	using Runtime.BoundTree;
	using Utilities;

	/// <summary>
	///     Classifies the operations performed on a variable.
	/// </summary>
	internal class VariableAccessClassifier : BoundTreeWalker
	{
		/// <summary>
		///     The default instance of the classifier.
		/// </summary>
		private static readonly VariableAccessClassifier _instance = new VariableAccessClassifier();

		/// <summary>
		///     Indicates which operations are performed on the variable.
		/// </summary>
		private VariableOperations _operations;

		/// <summary>
		///     The variable that is currently being classified.
		/// </summary>
		private VariableMetadata _variable;

		/// <summary>
		///     A value greater than 0 indicates whether we're currently checking for the variable within a write context.
		/// </summary>
		private int _writeContext;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		private VariableAccessClassifier()
		{
		}

		/// <summary>
		///     Classifies the operations performed on the <paramref name="variable" /> within the <paramref name="node" />.
		/// </summary>
		/// <param name="node">The node of a bound tree the <paramref name="variable" /> should be classified for.</param>
		/// <param name="variable">The variable that should be classified.</param>
		public static VariableOperations Classify(BoundNode node, VariableMetadata variable)
		{
			Requires.NotNull(node, () => node);
			Requires.NotNull(variable, () => variable);

			_instance._writeContext = 0;
			_instance._operations = VariableOperations.None;
			_instance._variable = variable;
			_instance.Visit(node);

			Assert.That(_instance._writeContext == 0, "Unbalanced write context operations.");
			return _instance._operations;
		}

		/// <summary>
		///     Visits an element of type <see cref="ArgumentExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="ArgumentExpression" /> instance that should be visited.</param>
		protected internal override void VisitArgumentExpression(ArgumentExpression expression)
		{
			if (expression.RefKind == RefKind.None)
				base.VisitArgumentExpression(expression);
			else
			{
				++_writeContext;
				base.VisitArgumentExpression(expression);
				--_writeContext;
			}
		}

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal override void VisitAssignmentStatement(AssignmentStatement statement)
		{
			++_writeContext;
			Visit(statement.AssignmentTarget);

			--_writeContext;
			Visit(statement.Expression);
		}

		/// <summary>
		///     Visits an element of type <see cref="VariableExpression" />.
		/// </summary>
		/// <param name="expression">The <see cref="VariableExpression" /> instance that should be visited.</param>
		protected internal override void VisitVariableExpression(VariableExpression expression)
		{
			if (expression.Variable != _variable)
				return;

			if (_writeContext > 0)
				_operations |= VariableOperations.Write;
			else
				_operations |= VariableOperations.Read;
		}
	}
}