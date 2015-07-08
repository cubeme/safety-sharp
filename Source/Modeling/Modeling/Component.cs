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
		///     Gets or sets the metadata of the currently active state of the component or <c>null</c> if there is none.
		/// </summary>
		internal StateMetadata StateMetadata
		{
			get { return _state == -1 ? null : Metadata.StateMachine.States[_state]; }
			set
			{
				Requires.NotNull(value, () => value);
				_state = value.Identifier;
			}
		}

		/// <summary>
		///     Gets the component's current state.
		/// </summary>
		public State State
		{
			get { return new State(StateMetadata == null ? null : StateMetadata.EnumValue); }
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
			if (StateMetadata != null)
				StateMetadata = StateMetadata.Update();
		}

		/// <summary>
		///     Creates the method body for the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private MethodBodyMetadata UpdateMethodBody()
		{
			if (Metadata.StateMachine == null)
				return new MethodBodyMetadata(new VariableMetadata[0], new VariableMetadata[0], new BlockStatement());

			VariableMetadata[] localVariables;
			BlockStatement body;

			Statement.CreateStateMachineCode(Metadata.StateMachine, out body, out localVariables);
			return new MethodBodyMetadata(new VariableMetadata[0], localVariables, body);
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