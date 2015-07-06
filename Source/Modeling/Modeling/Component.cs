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

namespace SafetySharp.Modeling
{
	using System;
	using System.Diagnostics;
	using System.Linq;
	using CompilerServices;
	using JetBrains.Annotations;
	using Runtime;
	using Runtime.BoundTree;
	using Utilities;

	/// <summary>
	///     Represents a S# component.
	/// </summary>
	[Metadata("InitializeMetadata")]
	public abstract class Component : MetadataObject<ComponentMetadata, ComponentMetadata.Builder>, IComponent
	{
		/// <summary>
		///     The identifier of the currently state.
		/// </summary>
		private int _state = -1;

		[UsedImplicitly]
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Action _updateMethod = null;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		protected Component()
			: this(null)
		{
		}

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="name">The name of the component.</param>
		protected Component(string name)
			: base(obj => new ComponentMetadata.Builder((Component)obj))
		{
			if (!String.IsNullOrWhiteSpace(name))
				MetadataBuilder.WithName(name);
		}

		/// <summary>
		///     Gets or sets the currently active state of the component or <c>null</c> if there is none.
		/// </summary>
		internal StateMetadata State
		{
			get { return _state == -1 ? null : Metadata.StateMachine.States[_state]; }
			set
			{
				Requires.NotNull(value, () => value);
				_state = value.Identifier;
			}
		}

		/// <summary>
		///     Gets all required ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic RequiredPorts
		{
			get
			{
				Requires.CompilationTransformation();
				return null;
			}
		}

		/// <summary>
		///     Gets all provided ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic ProvidedPorts
		{
			get
			{
				Requires.CompilationTransformation();
				return null;
			}
		}

		/// <summary>
		///     Updates the internal state of the component.
		/// </summary>
		[BackingField("_updateMethod")]
		[IntendedBehavior("UpdateBehavior")]
		[MethodBodyMetadata("UpdateMethodBody")]
		public virtual void Update()
		{
			_updateMethod();
		}

		/// <summary>
		///     Gets a value indicating whether this component is currently in <paramref name="state" />.
		/// </summary>
		/// <typeparam name="TState">The type of the state that should be checked.</typeparam>
		/// <param name="state">The state that should be checked.</param>
		public bool InState<TState>(TState state)
			where TState : struct, IConvertible
		{
			return _state != -1 && State.EnumValue.Equals(state);
		}

		/// <summary>
		///     Gets the current state of the component.
		/// </summary>
		/// <typeparam name="TState">The type of the state.</typeparam>
		public TState GetCurrentState<TState>()
			where TState : struct, IConvertible
		{
			Requires.That(State != null, "Component has no state.");
			return (TState)State.EnumValue;
		}

		/// <summary>
		///     Initializes the metadata of the class.
		/// </summary>
		[UsedImplicitly]
		private void InitializeMetadata()
		{
			MetadataBuilder.WithStepMethod(ReflectionHelpers.GetMethod(typeof(Component), "Update", Type.EmptyTypes, typeof(void)));
		}

		/// <summary>
		///     The default behavior of the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private void UpdateBehavior()
		{
			if (State != null)
				State = State.Update();
		}

		/// <summary>
		///     Creates the method body for the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private MethodBodyMetadata UpdateMethodBody()
		{
			if (Metadata.StateMachine == null)
				return new MethodBodyMetadata(new VariableMetadata[0], new VariableMetadata[0], new BlockStatement());

			// If guards are shared, only execute them once
			var transitions = Metadata.StateMachine.Transitions;
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
				var inState = new BinaryExpression(BinaryOperator.Equals,
					new FieldExpression(Metadata.StateMachine.StateField),
					new IntegerLiteralExpression(groupedTransitions[0].SourceState.Identifier));

				inState = groupedTransitions.Skip(1).Aggregate(inState, (expression, transition) =>
					new BinaryExpression(BinaryOperator.Or, expression,
						new BinaryExpression(BinaryOperator.Equals,
							new FieldExpression(Metadata.StateMachine.StateField),
							new IntegerLiteralExpression(transition.SourceState.Identifier))));

				return group.Key.Guard == null
					? inState
					: new BinaryExpression(BinaryOperator.And, inState, new VariableExpression(guardVariableLookup[group.Key.Guard]));
			}).ToArray();

			// Generate the statements for the transitions that execute the optional action and update the target state
			var statements = transitionGroups.Select(group =>
			{
				var stateUpdate = new AssignmentStatement(
					new FieldExpression(Metadata.StateMachine.StateField),
					new IntegerLiteralExpression(group.Key.TargetState.Identifier));

				if (group.Key.Action == null)
					return (Statement)stateUpdate;

				var action = new ExpressionStatement(new MethodInvocationExpression(group.Key.Action));
				return new BlockStatement(action, stateUpdate);
			}).ToArray();

			// Now put everything together
			var guardAssignments = guards.Select(guard => guard.Assignment);
			var guardLocals = guards.Select(guard => guard.Variable);

			var choiceStatement = new ChoiceStatement(guardConditions, statements, isDeterministic: false);
			var body = new BlockStatement(guardAssignments.Cast<Statement>().Concat(new[] { choiceStatement }).ToArray());

			return new MethodBodyMetadata(new VariableMetadata[0], guardLocals, body);
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the current component's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		protected static void SetInitialValues<T>(T field, params T[] values)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Adds the <paramref name="portBinding" /> to the current component's bindings.
		/// </summary>
		/// <param name="portBinding">
		///     The port binding expression of the form
		///     <c>component1.RequiredPorts.Port1 = component2.ProvidedPorts.Port2</c> that declares the binding.
		/// </param>
		protected static void Bind(object portBinding)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Adds a transition to the component's finite state machine.
		/// </summary>
		/// <typeparam name="TSourceState">An enumeration type representing the type of the source state.</typeparam>
		/// <typeparam name="TTargetState">An enumeration type representing the type of the target state.</typeparam>
		/// <param name="from">The source state that should be left by the transition.</param>
		/// <param name="to">The target state that should be entered by the transition.</param>
		/// <param name="guard">
		///     The guard that determines whether the transition can be taken. A value of <c>null</c>
		///     indicates that the transition can always be taken when the state machine is in the source state.
		/// </param>
		/// <param name="action">
		///     The action that should be executed when the transition is taken. A value of <c>null</c> indicates that
		///     no action should be performed when the transition is taken.
		/// </param>
		protected static void Transition<TSourceState, TTargetState>(TSourceState from, TTargetState to,
																	 Func<bool> guard = null, Action action = null)
			where TSourceState : struct, IConvertible
			where TTargetState : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Indicates that the component's state machine can initially be in <paramref name="initialState" />. If other initial
		///     states have previously been set for the state machine, the state machine can initially be in any of these states in
		///     addition to <paramref name="initialState" />; i.e., the previously set initial states are not overwritten.
		/// </summary>
		/// <param name="initialState">One of the initial states of the state machine.</param>
		protected static void InitialState<TState>(TState initialState)
			where TState : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Indicates that the component's state machine can initially be in the <paramref name="initialStates" />. If other initial
		///     states have previously been set for the state machine, the state machine can initially be in any of these states in
		///     addition to <paramref name="initialStates" />; i.e., the previously set initial states are not overwritten.
		/// </summary>
		/// <param name="initialStates">Some of the initial states of the state machine.</param>
		protected static void InitialStates<TState>(params TState[] initialStates)
			where TState : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}
	}
}