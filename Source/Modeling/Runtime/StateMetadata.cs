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
		///     The random number generator that is used to nondeterministically select one of the enabled transitions.
		/// </summary>
		private static readonly Random _random = new Random();

		/// <summary>
		///     The component the state belongs to.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     A cached list that is used to store the indices of the currently enabled transitions.
		/// </summary>
		private readonly List<int> _enabledTransitions = new List<int>();

		/// <summary>
		///     The transitions entering this state.
		/// </summary>
		private readonly Lazy<IReadOnlyList<TransitionMetadata>> _incomingTransitions;

		/// <summary>
		///     The transitions leaving this state.
		/// </summary>
		private readonly Lazy<IReadOnlyList<TransitionMetadata>> _outgoingTransitions;

		/// <summary>
		///     The predecessor states of this state.
		/// </summary>
		private readonly Lazy<IReadOnlyList<StateMetadata>> _predecessorStates;

		/// <summary>
		///     The successor states of this state.
		/// </summary>
		private readonly Lazy<IReadOnlyList<StateMetadata>> _successorStates;

		/// <summary>
		///     The priority overrides that affects the nondeterministic selection of enabled transitions.
		/// </summary>
		private int[] _priorityOverrides;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the state belongs to.</param>
		/// <param name="identifier">The identifier of the state.</param>
		/// <param name="name">The user-friendly name of the state.</param>
		/// <param name="enumValue">The original enumeration literal that was used to create the state.</param>
		internal StateMetadata(Component component, int identifier, string name, object enumValue)
		{
			Requires.NotNull(component, () => component);
			Requires.That(identifier >= 0, () => identifier, "The identifier must be equal to or greater than 0.");
			Requires.NotNullOrWhitespace(name, () => name);
			Requires.NotNull(enumValue, () => enumValue);

			Identifier = identifier;
			Name = name;
			EnumValue = enumValue;
			_component = component;

			_incomingTransitions = new Lazy<IReadOnlyList<TransitionMetadata>>(
				() => StateMachine.Transitions.Where(transition => transition.TargetState == this).ToArray());

			_outgoingTransitions = new Lazy<IReadOnlyList<TransitionMetadata>>(
				() => StateMachine.Transitions.Where(transition => transition.SourceState == this).ToArray());

			_successorStates = new Lazy<IReadOnlyList<StateMetadata>>(
				() => OutgoingTransitions.Select(transition => transition.TargetState).Distinct().ToArray());

			_predecessorStates = new Lazy<IReadOnlyList<StateMetadata>>(
				() => IncomingTransitions.Select(transition => transition.SourceState).Distinct().ToArray());
		}

		/// <summary>
		///     The original enumeration literal that was used to create the state.
		/// </summary>
		public object EnumValue { get; private set; }

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
		public IReadOnlyList<TransitionMetadata> OutgoingTransitions
		{
			get { return _outgoingTransitions.Value; }
		}

		/// <summary>
		///     Gets the transitions entering this state.
		/// </summary>
		public IReadOnlyList<TransitionMetadata> IncomingTransitions
		{
			get { return _incomingTransitions.Value; }
		}

		/// <summary>
		///     Gets the successor states of the state that have incoming transitions from this state.
		/// </summary>
		public IReadOnlyList<StateMetadata> SuccessorStates
		{
			get { return _successorStates.Value; }
		}

		/// <summary>
		///     Gets the predecessors states of the state that have outgoing transitions to this state.
		/// </summary>
		public IReadOnlyList<StateMetadata> PredecessorStates
		{
			get { return _predecessorStates.Value; }
		}

		/// <summary>
		///     Gets the priority overrides that can be used to (partially or fully) override the nondeterministic selection
		///     of outgoing transitions.
		/// </summary>
		public int[] PriorityOverrides
		{
			get { return _priorityOverrides ?? (_priorityOverrides = new int[OutgoingTransitions.Count]); }
		}

		/// <summary>
		///     Resets the <see cref="PriorityOverrides" /> property to its initial value.
		/// </summary>
		public void ResetPriorityOverrides()
		{
			for (var i = 0; i < OutgoingTransitions.Count; ++i)
				PriorityOverrides[i] = 0;
		}

		/// <summary>
		///     Checks whether any transitions are active and changes the state accordingly.
		/// </summary>
		internal StateMetadata Update()
		{
			_enabledTransitions.Clear();

			// Determine the enabled transitions
			for (var i = 0; i < OutgoingTransitions.Count; ++i)
			{
				if (OutgoingTransitions[i].IsCurrentlyEnabled())
					_enabledTransitions.Add(i);
			}

			// If there are no enabled transitions, don't change the state
			if (_enabledTransitions.Count == 0)
				return this;

			// If there is only one enabled transition, take it; otherwise, select one nondeterministically
			int chosenTransition;
			if (_enabledTransitions.Count == 1)
				chosenTransition = _enabledTransitions[0];
			else
			{
				// Remove all enabled transitions whose dynamic priority is too low
				var maxPriority = _enabledTransitions.Select(transition => PriorityOverrides[transition]).Max();
				for (var i = 0; i < _enabledTransitions.Count; ++i)
				{
					if (PriorityOverrides[_enabledTransitions[i]] < maxPriority)
						_enabledTransitions.RemoveAt(i--);
				}

				// If we've now ruled out all nondeterminism, take the transition with the highest dynamic priority
				if (_enabledTransitions.Count == 1)
					chosenTransition = _enabledTransitions[0];

				// Otherwise, nondeterministically choose one of the remaining transitions
				chosenTransition = _enabledTransitions[_random.Next(0, _enabledTransitions.Count)];
			}

			// Execute the transition's action and return the new state
			OutgoingTransitions[chosenTransition].ExecuteAction();
			return OutgoingTransitions[chosenTransition].TargetState;
		}
	}
}