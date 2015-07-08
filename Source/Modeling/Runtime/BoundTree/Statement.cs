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
	using System.Linq;
	using Transformation;
	using Utilities;

	/// <summary>
	///     Represents an expression within a S# method.
	/// </summary>
	public abstract class Statement : BoundNode
	{
		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override sealed string ToString()
		{
			var serializer = new CSharpSerializer();
			return serializer.Serialize(this);
		}

		/// <summary>
		///     Creates the <paramref name="statement" /> and <paramref name="localVariables" /> that implement the
		///     <paramref name="stateMachine" />.
		/// </summary>
		/// <param name="stateMachine">The state machine the code should be generated for.</param>
		/// <param name="statement">Returns the block statement representing the code generated for the state machine.</param>
		/// <param name="localVariables">Returns the local variables used by the <paramref name="statement" />.</param>
		internal static void CreateStateMachineCode(StateMachineMetadata stateMachine, out BlockStatement statement,
													out VariableMetadata[] localVariables)
		{
			Requires.NotNull(stateMachine, () => stateMachine);

			// If guards are shared, only execute them once
			var transitions = stateMachine.Transitions;
			var guards = transitions
				.Select(transition => transition.Guard)
				.Where(guard => guard != null)
				.Distinct()
				.Select((guard, index) =>
				{
					var variable = new VariableMetadata("guard" + index, typeof(bool));
					return new
					{
						Guard = guard,
						Variable = variable,
						Assignment = new AssignmentStatement(new VariableExpression(variable), new MethodInvocationExpression(guard))
					};
				})
				.ToArray();

			var guardVariableLookup = guards.ToDictionary(guard => guard.Guard, guard => guard.Variable);

			// Similarily, optimize the case where multiple transitions have the same target state, the same guard, and the same action
			var transitionGroups = transitions.GroupBy(transition => new { transition.TargetState, transition.Guard, transition.Action });
			var guardConditions = transitionGroups.Select(group =>
			{
				var groupedTransitions = group.ToArray();
				var inState = (Expression)new BinaryExpression(BinaryOperator.Equals,
					new FieldExpression(stateMachine.StateField),
					new IntegerLiteralExpression(groupedTransitions[0].SourceState.Identifier));

				inState = groupedTransitions.Skip(1).Aggregate(inState, (expression, transition) =>
					new BinaryExpression(BinaryOperator.Or, expression,
						new BinaryExpression(BinaryOperator.Equals,
							new FieldExpression(stateMachine.StateField),
							new IntegerLiteralExpression(transition.SourceState.Identifier))));

				return group.Key.Guard == null
					? inState
					: new BinaryExpression(BinaryOperator.And, inState, new VariableExpression(guardVariableLookup[group.Key.Guard]));
			}).ToArray();

			// Generate the statements for the transitions that execute the optional action and update the target state
			var statements = transitionGroups.Select(group =>
			{
				var stateUpdate = new AssignmentStatement(
					new FieldExpression(stateMachine.StateField),
					new IntegerLiteralExpression(group.Key.TargetState.Identifier));

				if (group.Key.Action == null)
					return (Statement)stateUpdate;

				var action = new ExpressionStatement(new MethodInvocationExpression(group.Key.Action));
				return new BlockStatement(action, stateUpdate);
			}).ToArray();

			// Generate the tau transition that is taken whenever no other transition is enabled
			var tauCondition = guardConditions.Skip(1).Aggregate((Expression)new UnaryExpression(UnaryOperator.Not, guardConditions[0]),
				(tauGuard, guard) => new BinaryExpression(BinaryOperator.And, new UnaryExpression(UnaryOperator.Not, guard), tauGuard));
			var tauStatement = BlockStatement.Empty;

			// Now put everything together into the choice statement
			guardConditions = guardConditions.Concat(new[] { tauCondition }).ToArray();
			statements = statements.Concat(new[] { tauStatement }).ToArray();
			var choiceStatement = new ChoiceStatement(guardConditions, statements, isDeterministic: false);

			// Generate and return the final statement that assigns all guards and executes the choice
			var guardAssignments = guards.Select(guard => guard.Assignment);
			statement = new BlockStatement(guardAssignments.Cast<Statement>().Concat(new[] { choiceStatement }).ToArray());

			// Return the local variables generated for the state machine
			localVariables = guards.Select(guard => guard.Variable).ToArray();
		}
	}
}