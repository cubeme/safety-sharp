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

namespace SafetySharp.Runtime
{
	using System;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a state machine transition.
	/// </summary>
	public sealed class TransitionMetadata
	{
		/// <summary>
		///     The component the transition belongs to.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the transition belongs to.</param>
		/// <param name="sourceState">The source state that should be left by the transition.</param>
		/// <param name="targetState">The target state that should be entered by the transition.</param>
		/// <param name="guard">The guard that determines whether the transition can be taken.</param>
		/// <param name="action">The action that should be executed when the transition is taken.</param>
		internal TransitionMetadata(Component component, StateMetadata sourceState, StateMetadata targetState,
									GuardMetadata guard, ActionMetadata action)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(sourceState, () => sourceState);
			Requires.NotNull(targetState, () => targetState);

			_component = component;
			SourceState = sourceState;
			TargetState = targetState;
			Guard = guard;
			Action = action;
		}

		/// <summary>
		///     Gets the source state that is left by the transition.
		/// </summary>
		public StateMetadata SourceState { get; private set; }

		/// <summary>
		///     Gets the target state that is entered by the transition.
		/// </summary>
		public StateMetadata TargetState { get; private set; }

		/// <summary>
		///     Gets the guard that determines whether the transition can be taken. A value of <c>null</c>
		///     indicates that the transition can always be taken when the state machine is in the source state.
		/// </summary>
		public GuardMetadata Guard { get; private set; }

		/// <summary>
		///     Gets the action that is executed when the transition is taken. A value of <c>null</c> indicates that
		///     no action should be performed when the transition is taken.
		/// </summary>
		public ActionMetadata Action { get; private set; }

		/// <summary>
		///     Gets the <see cref="StateMachineMetadata" /> the transition belongs to.
		/// </summary>
		public StateMachineMetadata StateMachine
		{
			get { return _component.Metadata.StateMachine; }
		}

		/// <summary>
		///     Checks the transition's <see cref="Guard" /> to check if the transition is currently enabled.
		/// </summary>
		public bool IsCurrentlyEnabled()
		{
			if (Guard == null)
				return true;

			return Guard.Execute();
		}

		/// <summary>
		///     Executes the transition's <see cref="Action" /> if there is one.
		/// </summary>
		public void ExecuteAction()
		{
			if (Action != null)
				Action.Execute();
		}
	}
}