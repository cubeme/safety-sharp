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
	using System.Linq;
	using Runtime;
	using Runtime.BoundTree;
	using Utilities;

	/// <summary>
	///     Inlines <see cref="MethodInvocationExpression" />s within <see cref="MethodBodyMetadata" /> instances recursively.
	///     Assumes that there are no cycles in the method call graph.
	/// </summary>
	internal class MethodInliner : BoundTreeRewriter
	{
		/// <summary>
		///     The list of local variables of the new inlined method.
		/// </summary>
		private readonly List<VariableMetadata> _localVariables = new List<VariableMetadata>();

		/// <summary>
		///     The name scope that is used to create unique variables names.
		/// </summary>
		private readonly NameScope _nameScope = new NameScope();

		/// <summary>
		///     The predicate that indicates whether an invoked method should be inlined.
		/// </summary>
		private readonly Func<MethodMetadata, bool> _predicate;

		/// <summary>
		///     Used to replace method argument variables with their actual expressions.
		/// </summary>
		private readonly VariableReplacer _variableReplacer = new VariableReplacer();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="predicate">The predicate that indicates whether an invoked method should be inlined.</param>
		private MethodInliner(Func<MethodMetadata, bool> predicate)
		{
			_predicate = predicate;
		}

		/// <summary>
		///     Recursively inlines all methods invoked within <paramref name="method" />'s body.
		/// </summary>
		/// <param name="method">The method which should have all invoked methods inlined.</param>
		public static MethodBodyMetadata Inline(MethodMetadata method)
		{
			Requires.NotNull(method, () => method);
			return Inline(method.MethodBody, _ => true);
		}

		/// <summary>
		///     Recursively inlines all methods invoked within the <paramref name="methodBody" /> for which the
		///     <paramref name="predicate" /> returns <c>true</c>.
		/// </summary>
		/// <param name="methodBody">The method body which should have all invoked methods inlined.</param>
		/// <param name="predicate">The predicate that indicates whether an invoked method should be inlined.</param>
		internal static MethodBodyMetadata Inline(MethodBodyMetadata methodBody, Func<MethodMetadata, bool> predicate)
		{
			Requires.NotNull(methodBody, () => methodBody);

			var inliner = new MethodInliner(predicate);
			inliner._nameScope.AddRange(methodBody.Parameters.Select(parameter => parameter.Name));

			var body = inliner._variableReplacer.Visit(inliner.Inline(methodBody));
			return new MethodBodyMetadata(methodBody.Parameters, inliner._localVariables, (BlockStatement)body);
		}

		/// <summary>
		///     Recursively inlines all methods invoked within <paramref name="methodBody" />'s body.
		/// </summary>
		/// <param name="methodBody">The method which should have all invoked methods inlined.</param>
		private BoundNode Inline(MethodBodyMetadata methodBody)
		{
			foreach (var variable in methodBody.LocalVariables)
				ReplaceWithNewLocalVariable(variable);

			return Visit(methodBody.Body);
		}

		/// <summary>
		///     Visits an element of type <see cref="ExpressionStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="ExpressionStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitExpressionStatement(ExpressionStatement statement)
		{
			var invocationExpression = statement.Expression as MethodInvocationExpression;
			if (invocationExpression == null || !_predicate(invocationExpression.Method))
				return statement;

			ReplaceReadonlyArguments(invocationExpression);
			var assignments = ReplaceOverwrittenArguments(invocationExpression);
			var inlinedBody = (Statement)Inline(invocationExpression.Method.MethodBody);

			return new BlockStatement(assignments.Concat(new[] { inlinedBody }).ToArray());
		}

		/// <summary>
		///     Visits an element of type <see cref="AssignmentStatement" />.
		/// </summary>
		/// <param name="statement">The <see cref="AssignmentStatement" /> instance that should be visited.</param>
		protected internal override BoundNode VisitAssignmentStatement(AssignmentStatement statement)
		{
			var invocationExpression = statement.Expression as MethodInvocationExpression;
			if (invocationExpression == null || !_predicate(invocationExpression.Method))
				return statement;

			// There are two possibilities: 
			//    (1) The method consists of a single return statement only
			//    (2) The method consists of multiple statements

			var methodBody = invocationExpression.Method.MethodBody;
			var body = methodBody.Body;
			var returnStatement = body.Statements[body.Statements.Count - 1] as ReturnStatement;
			Assert.NotNull(returnStatement, "Expected a return statement at the end of the method body.");

			if (body.Statements.Count == 1)
			{
				// For case (1), rewrite the assignment by replacing the right-hand side with the inlined method's expression.
				Assert.That(!methodBody.LocalVariables.Any(), "Method unexpectedly has local variables.");

				ReplaceReadonlyArguments(invocationExpression);
				return new AssignmentStatement(statement.AssignmentTarget, returnStatement.Expression);
			}

			// For case (2), replace the method's return variable with the assignment target,
			// and replace this assignment with the method's body
			ReplaceReadonlyArguments(invocationExpression);
			var assignments = ReplaceOverwrittenArguments(invocationExpression);
			var inlinedBody = (Statement)Inline(invocationExpression.Method.MethodBody);
			var inlinedInvocation = new BlockStatement(assignments.Concat(new[] { inlinedBody }).ToArray());

			// Assign the method's return value directly to this assignment's assignment target
			var returnVariable = returnStatement.Expression as VariableExpression;
			Assert.NotNull(returnVariable, "Expected the return statement's expression to be a reference to a variable.");

			_variableReplacer.AddVariableReplacement(returnVariable.Variable, statement.AssignmentTarget);
			return inlinedInvocation;
		}

		/// <summary>
		///     Handles the replacement of the <paramref name="invocation" />'s arguments that are read-only.
		/// </summary>
		private void ReplaceReadonlyArguments(MethodInvocationExpression invocation)
		{
			_variableReplacer.AddArgumentReplacements(invocation);
		}

		/// <summary>
		///     Handles the replacement of the <paramref name="invocation" />'s arguments whose value is potentially overwritten during
		///     the execution of the method.
		/// </summary>
		private IEnumerable<Statement> ReplaceOverwrittenArguments(MethodInvocationExpression invocation)
		{
			var methodBody = invocation.Method.MethodBody;
			var parameters = methodBody.Parameters.ToArray();
			var arguments = invocation.Arguments.ToArray();

			Assert.That(parameters.Length == arguments.Length, "Parameters and arguments don't match up.");

			for (var i = 0; i < parameters.Length; ++i)
			{
				if (arguments[i].RefKind != RefKind.None || !VariableAccessClassifier.Classify(methodBody.Body, parameters[i]).IsWritten())
					continue;

				var variable = ReplaceWithNewLocalVariable(parameters[i]);
				yield return new AssignmentStatement(new VariableExpression(variable), arguments[i]);
			}
		}

		/// <summary>
		///     Generates a new, uniquely-named local replacement variable for <paramref name="variable" />.
		/// </summary>
		private VariableMetadata ReplaceWithNewLocalVariable(VariableMetadata variable)
		{
			var uniqueName = _nameScope.MakeUnique(variable.Name);
			var replacingVariable = new VariableMetadata(uniqueName, variable.Type, isParameter: false);

			_localVariables.Add(replacingVariable);
			_variableReplacer.AddVariableReplacement(variable, new VariableExpression(replacingVariable));

			return replacingVariable;
		}
	}
}