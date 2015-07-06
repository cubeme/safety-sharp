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
	using System.Linq;
	using System.Reflection;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a transition action.
	/// </summary>
	public sealed class ActionMetadata : MethodMetadata
	{
		/// <summary>
		///     The delegate that can be used to execute the guard.
		/// </summary>
		private readonly Action _delegate;

		/// <summary>
		///     The metadata of the transition the action belongs to.
		/// </summary>
		private readonly Lazy<TransitionMetadata> _transition;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the action belongs to.</param>
		/// <param name="method">The CLR method the metadata should be provided for.</param>
		/// <param name="name">The name of the method; if <c>null</c>, the method's CLR name is used.</param>
		internal ActionMetadata(IMetadataObject obj, MethodInfo method, string name = null)
			: base(obj, method, name)
		{
			Requires.That(HasImplementation, () => method, "Transition actions must have an implementation.");
			Requires.That(CanBeAffectedByFaultEffects, () => method, "Transition actions must be sensitive to fault effects.");
			Requires.That(method.GetParameters().Length == 0, () => method, "A transition action cannot take any parameters.");
			Requires.That(method.ReturnType == typeof(void), () => method, "A transition action must not return a value.");

			_transition = new Lazy<TransitionMetadata>(() => DeclaringObject.StateMachine.Transitions.Single(transition => transition.Action == this));
			_delegate = (Action)CreateDelegate(typeof(Action));
		}

		/// <summary>
		///     Gets the metadata of the declaring component.
		/// </summary>
		public new ComponentMetadata DeclaringObject
		{
			get { return ((ComponentMetadata)base.DeclaringObject); }
		}

		/// <summary>
		///     Gets the metadata of the transition the action belongs to.
		/// </summary>
		public TransitionMetadata Transition
		{
			get { return _transition.Value; }
		}

		/// <summary>
		///     Executes the guard, returning <c>true</c> to indicate that the guard holds.
		/// </summary>
		public void Execute()
		{
			_delegate();
		}
	}
}