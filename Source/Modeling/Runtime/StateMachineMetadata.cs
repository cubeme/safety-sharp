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
	///     Represents the immutable data of a S# finite state machine.
	/// </summary>
	public sealed class StateMachineMetadata
	{
		/// <summary>
		///     The random number generator that is used to nondeterministically select one of the initial states.
		/// </summary>
		private static readonly Random _random = new Random();

		/// <summary>
		///     The metadata of the declaring component.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the state machine belongs to.</param>
		/// <param name="stateField">The field that should be used to store the component's current state.</param>
		/// <param name="states">The states of the state machine.</param>
		/// <param name="initialStates">The initial states of the state machine.</param>
		/// <param name="transitions">The transitions of the state machine.</param>
		internal StateMachineMetadata(Component component, FieldMetadata stateField, IEnumerable<StateMetadata> states,
									  IEnumerable<StateMetadata> initialStates, IEnumerable<TransitionMetadata> transitions)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(states, () => states);
			Requires.NotNull(transitions, () => transitions);
			Requires.NotNull(stateField, () => stateField);

			var stateArray = states.ToArray();
			var initialStatesArray = initialStates.Distinct().ToArray();
			var transitionArray = transitions.ToArray();

			Requires.That(initialStatesArray.Length > 0, "An initial state must be set for the state machine.");

			_component = component;

			States = stateArray;
			InitialStates = initialStatesArray;
			Transitions = transitionArray;
			StateField = stateField;

			_component.State = InitialStates[_random.Next(0, InitialStates.Count)];
		}

		/// <summary>
		///     Gets the metadata of the field storing the component's current state.
		/// </summary>
		public FieldMetadata StateField { get; private set; }

		/// <summary>
		///     Gets the metadata of the declaring component.
		/// </summary>
		public ComponentMetadata DeclaringComponent
		{
			get { return _component.Metadata; }
		}

		/// <summary>
		///     Gets the metadata for the <paramref name="state" />.
		/// </summary>
		/// <param name="state">The state the metadata should be retrieved for.</param>
		public StateMetadata this[object state]
		{
			get
			{
				var metadata = States.SingleOrDefault(s => s.EnumValue.Equals(state));
				Requires.That(metadata != null, () => state, "Unknown state.");

				return metadata;
			}
		}

		/// <summary>
		///     Gets the states of the state machine.
		/// </summary>
		public IReadOnlyList<StateMetadata> States { get; private set; }

		/// <summary>
		///     Gets the initial states of the state machine.
		/// </summary>
		public IReadOnlyList<StateMetadata> InitialStates { get; private set; }

		/// <summary>
		///     Gets the transitions of the state machine.
		/// </summary>
		public IReadOnlyList<TransitionMetadata> Transitions { get; private set; }
	}
}