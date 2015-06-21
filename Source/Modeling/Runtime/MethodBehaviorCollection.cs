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
	///     Represents a collection of method behaviors, including the intended behavior of a method and its fault injections.
	/// </summary>
	public sealed class MethodBehaviorCollection
	{
		/// <summary>
		///     The S# object the affected method belongs to.
		/// </summary>
		private readonly IMetadataObject _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the affected method belongs to.</param>
		/// <param name="affectedMethod">The metadata of the S# method that should be affected by the fault injector.</param>
		internal MethodBehaviorCollection(IMetadataObject obj, MethodMetadata affectedMethod)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(affectedMethod, () => affectedMethod);

			_object = obj;
			AffectedMethod = affectedMethod;
			FaultEffects = Enumerable.Empty<FaultEffectMetadata>();
			FaultInjections = Enumerable.Empty<FaultInjection>().ToArray();

			// Create and inject the intended behavior now; we do that as early as possible so that all
			// methods can be called reliably in the model initialization phase
			IntendedBehavior = new IntendedBehavior(_object, affectedMethod);
			IntendedBehavior.Bind();
		}

		/// <summary>
		///     Gets the metadata of the S# method that is affected by the fault injector.
		/// </summary>
		public MethodMetadata AffectedMethod { get; private set; }

		/// <summary>
		///     Gets the intended behavior of the method. For undependable methods that can be affected by fault effects, the intended
		///     behavior is the method's behavior in the absence of any faults.
		/// </summary>
		public IntendedBehavior IntendedBehavior { get; private set; }

		/// <summary>
		///     Gets the fault injections of the method.
		/// </summary>
		public IReadOnlyList<FaultInjection> FaultInjections { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method is affected by fault effects.
		/// </summary>
		public bool IsAffectedByFaultEffects
		{
			get { return FaultEffects.Any(); }
		}

		/// <summary>
		///     Gets the metadata of the fault effects that affect the method.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> FaultEffects { get; private set; }

		/// <summary>
		///     Injects the affecting faults into the method.
		/// </summary>
		internal void InjectFaults()
		{
			var component = AffectedMethod.DeclaringObject as ComponentMetadata;
			Requires.That(component != null, "Fault injections are only supported for component methods.");

			// Bind the externally provided intended behavior, if necessary
			IntendedBehavior.BindExternal();

			// Determine all fault effects that affect the method
			FaultEffects = component
				.Faults
				.SelectMany(fault => fault.Effects)
				.Where(effect => effect.AffectedMethod.MethodInfo == AffectedMethod.MethodInfo)
				.ToArray();

			// Group the fault effects by priority, creating deterministic or nondeterministic fault injections appropriately;
			// the fault injections are sorted from highest to lowest priority
			FaultInjections = FaultEffects
				.GroupBy(behavior => behavior.Priority)
				.OrderByDescending(behaviorGroup => behaviorGroup.Key)
				.Select(behaviorGroup => behaviorGroup.Count() > 1
					? (FaultInjection)new NondeterministicFaultInjection(_object, AffectedMethod, behaviorGroup)
					: (FaultInjection)new DeterministicFaultInjection(_object, AffectedMethod, behaviorGroup.Single()))
				.ToArray();

			// Bind the behaviors, passing along the fallback behavior
			// This injects the fault behaviors and ensures that they're invoked in the right order
			for (var i = FaultInjections.Count; i > 0; --i)
			{
				var fallbackBehavior = i < FaultInjections.Count ? FaultInjections[i].Delegate : IntendedBehavior.Delegate;
				FaultInjections[i - 1].Bind(fallbackBehavior, AffectedMethod.MethodType);
			}
		}
	}
}