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
		internal StateMetadata CurrentState { get; set; }

		/// <summary>
		///     Gets all required ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic RequiredPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
		}

		/// <summary>
		///     Gets all provided ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic ProvidedPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
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
			return CurrentState != null && CurrentState.EnumValue.Equals(state);
		}

		/// <summary>
		///     Gets the current state of the component.
		/// </summary>
		/// <typeparam name="TState">The type of the state.</typeparam>
		public TState GetCurrentState<TState>()
			where TState : struct, IConvertible
		{
			Requires.That(CurrentState != null, "Component has no state.");
			return (TState)CurrentState.EnumValue;
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
		///     Empty default behavior of the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private void UpdateBehavior()
		{
			if (CurrentState != null)
				CurrentState = CurrentState.Update();
		}

		/// <summary>
		///     Creates the method body for the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private MethodBodyMetadata UpdateMethodBody()
		{
			return new MethodBodyMetadata(new VariableMetadata[0], new VariableMetadata[0],
				new BlockStatement());
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
		/// <typeparam name="TSource">An enumeration type representing the type of the source state.</typeparam>
		/// <typeparam name="TTarget">An enumeration type representing the type of the target state.</typeparam>
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
		protected static void AddTransition<TSource, TTarget>(TSource from, TTarget to, Func<bool> guard = null, Action action = null)
			where TSource : struct, IConvertible
			where TTarget : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Indicates that the component's state machine can initially be in <paramref name="initialState" />.
		/// </summary>
		/// <param name="initialState">One of the initial states of the state machine.</param>
		protected static void AddInitialState<TState>(TState initialState)
			where TState : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Indicates that the component's state machine can initially be in the <paramref name="initialStates" />.
		/// </summary>
		/// <param name="initialStates">Some of the initial states of the state machine.</param>
		protected static void AddInitialStates<TState>(params TState[] initialStates)
			where TState : struct, IConvertible
		{
			Requires.CompilationTransformation();
		}
	}
}