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
	using System.Collections.Generic;
	using System.Linq;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a <see cref="StateMachineMetadata" /> state.
	/// </summary>
	public sealed class StateMetadata
	{
		/// <summary>
		///     The component the state belongs to.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     The transitions entering this state.
		/// </summary>
		private readonly Lazy<IEnumerable<TransitionMetadata>> _incomingTransitions;

		/// <summary>
		///     The transitions leaving this state.
		/// </summary>
		private readonly Lazy<IEnumerable<TransitionMetadata>> _outgoingTransitions;

		/// <summary>
		///     The predecessor states of this state.
		/// </summary>
		private readonly Lazy<IEnumerable<StateMetadata>> _predecessorStates;

		/// <summary>
		///     The successor states of this state.
		/// </summary>
		private readonly Lazy<IEnumerable<StateMetadata>> _successorStates;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the state belongs to.</param>
		/// <param name="identifier">The identifier of the state.</param>
		/// <param name="name">The user-friendly name of the state.</param>
		internal StateMetadata(Component component, int identifier, string name)
		{
			Requires.NotNull(component, () => component);
			Requires.That(identifier >= 0, () => identifier, "The identifier must be equal to or greater than 0.");
			Requires.NotNullOrWhitespace(name, () => name);

			Identifier = identifier;
			Name = name;
			_component = component;

			_incomingTransitions = new Lazy<IEnumerable<TransitionMetadata>>(
				() => StateMachine.Transitions.Where(transition => transition.TargetState == this).ToArray());

			_outgoingTransitions = new Lazy<IEnumerable<TransitionMetadata>>(
				() => StateMachine.Transitions.Where(transition => transition.SourceState == this).ToArray());

			_successorStates = new Lazy<IEnumerable<StateMetadata>>(
				() => OutgoingTransitions.Select(transition => transition.TargetState).Distinct().ToArray());

			_predecessorStates = new Lazy<IEnumerable<StateMetadata>>(
				() => IncomingTransitions.Select(transition => transition.SourceState).Distinct().ToArray());
		}

		/// <summary>
		///     Gets the identifier of the state that is unique within its <see cref="StateMachine" />.
		/// </summary>
		public int Identifier { get; private set; }

		/// <summary>
		///     Gets the user-friendly name of the state.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Gets the <see cref="StateMachineMetadata" /> the state belongs to.
		/// </summary>
		public StateMachineMetadata StateMachine
		{
			get { return _component.Metadata.StateMachine; }
		}

		/// <summary>
		///     Gets the transitions leaving this state.
		/// </summary>
		public IEnumerable<TransitionMetadata> OutgoingTransitions
		{
			get { return _outgoingTransitions.Value; }
		}

		/// <summary>
		///     Gets the transitions entering this state.
		/// </summary>
		public IEnumerable<TransitionMetadata> IncomingTransitions
		{
			get { return _incomingTransitions.Value; }
		}

		/// <summary>
		///     Gets the successor states of the state that have incoming transitions from this state.
		/// </summary>
		public IEnumerable<StateMetadata> SuccessorStates
		{
			get { return _successorStates.Value; }
		}

		/// <summary>
		///     Gets the predecessors states of the state that have outgoing transitions to this state.
		/// </summary>
		public IEnumerable<StateMetadata> PredecessorStates
		{
			get { return _predecessorStates.Value; }
		}
	}
}