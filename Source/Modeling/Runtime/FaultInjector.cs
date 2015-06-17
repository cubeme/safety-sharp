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
	using Utilities;

	/// <summary>
	///     Injects fault effects into the behavior of undependable S# methods.
	/// </summary>
	public sealed class FaultInjector
	{
		/// <summary>
		///     The S# object the affected method belongs to.
		/// </summary>
		private readonly object _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the affected method belongs to.</param>
		/// <param name="affectedMethod">The metadata of the S# method that should be affected by the fault injector.</param>
		internal FaultInjector(object obj, MethodMetadata affectedMethod)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(affectedMethod, () => affectedMethod);

			_object = obj;
			AffectedMethod = affectedMethod;
			AffectingFaultEffects = Enumerable.Empty<FaultEffectMetadata>();

			// Create and inject the intended behavior now; we do that as early as possible so that all
			// methods can be called reliably in the model initialization phase
			var intendedBehavior = new IntendedBehavior(_object, affectedMethod);
			intendedBehavior.Bind(fallbackBehavior: null, delegateType: affectedMethod.MethodType);

			InjectedBehaviors = new[] { intendedBehavior };
		}

		/// <summary>
		///     Gets the metadata of the S# method that is affected by the fault injector.
		/// </summary>
		public MethodMetadata AffectedMethod { get; private set; }

		/// <summary>
		///     Gets the behaviors injected into the method. The last element of the list is guaranteed to be a
		///     <see cref="IntendedBehavior" /> instance representing the method's <see cref="MethodMetadata.IntendedBehavior" />.
		/// </summary>
		public IReadOnlyList<MethodBehavior> InjectedBehaviors { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method is affected by fault effects.
		/// </summary>
		public bool IsAffectedByFaultEffects
		{
			get { return AffectingFaultEffects.Any(); }
		}

		/// <summary>
		///     Gets the metadata of the fault effects that affect the method.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> AffectingFaultEffects { get; private set; }

		/// <summary>
		///     Injects the affecting faults into the method.
		/// </summary>
		internal void InjectFaults()
		{
			var component = AffectedMethod.DeclaringObject as ComponentMetadata;
			Requires.That(component != null, "Fault injections are only supported for component methods.");

			// Determine all fault effects that affect the method
			AffectingFaultEffects = component
				.Faults
				.SelectMany(fault => fault.FaultEffects)
				.Where(effect => effect.AffectedMethod.MethodInfo == AffectedMethod.MethodInfo)
				.ToArray();

			// Group the fault effects by priority, creating deterministic or nondeterministic method behaviors appropriately;
			// the behaviors are sorted from highest to lowest priority
			var behaviors = AffectingFaultEffects
				.GroupBy(behavior => behavior.Priority)
				.OrderByDescending(behaviorGroup => behaviorGroup.Key)
				.Select(behaviorGroup => behaviorGroup.Count() > 1
					? (MethodBehavior)new NondeterministicFaultBehavior(_object, AffectedMethod, behaviorGroup)
					: (MethodBehavior)new DeterministicFaultBehavior(_object, AffectedMethod, behaviorGroup.Single()))
				.ToList();

			// Complete the list of injected behaviors by appending the intended behavior at the end
			Assert.That(InjectedBehaviors.Count == 1, "Expected to find the intended behavior.");

			var intendedBehavior = InjectedBehaviors[0] as IntendedBehavior;
			Assert.NotNull(intendedBehavior, "Expected to find the intended behavior.");

			intendedBehavior.BindExternal();
			behaviors.Add(intendedBehavior);

			InjectedBehaviors = behaviors.AsReadOnly();

			// Bind the behaviors, passing along the fallback behavior
			// This injects the fault behaviors and ensures that they're invoked in the right order
			for (var i = InjectedBehaviors.Count; i > 0; --i)
				InjectedBehaviors[i - 1].Bind(i < InjectedBehaviors.Count ? InjectedBehaviors[i] : null, AffectedMethod.MethodType);
		}
	}
}