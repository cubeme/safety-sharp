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
	using System.Linq.Expressions;
	using JetBrains.Annotations;
	using Utilities;

	/// <summary>
	///     Represents a nondeterministic set of fault effects that selects and executes one effect nondeterministically instead of
	///     the fallback behavior when one or more of its corresponding faults are active.
	/// </summary>
	public sealed class NondeterministicFaultBehavior : MethodBehavior
	{
		/// <summary>
		///     The random number generator that is used to nondeterministically select one of the enabled fault effects.
		/// </summary>
		private static readonly Random _random = new Random();

		/// <summary>
		///     A cached list that is used to store the indices of the currently enabled fault effects.
		/// </summary>
		private readonly List<int> _enabledFaultEffects = new List<int>();

		/// <summary>
		///     The metadata of the fault effects that are injected nondeterministically.
		/// </summary>
		private readonly FaultEffectMetadata[] _faultEffects;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the behavior belongs to.</param>
		/// <param name="faultEffects">The fault effects that should be injected nondeterministically.</param>
		public NondeterministicFaultBehavior(object obj, MethodMetadata method, IEnumerable<FaultEffectMetadata> faultEffects)
			: base(obj, method)
		{
			Requires.NotNull(faultEffects, () => faultEffects);

			_faultEffects = faultEffects.ToArray();

			PriorityOverrides = new int[_faultEffects.Length];
			ResetPriorityOverrides();
		}

		/// <summary>
		///     Gets the metadata of the fault effects that are injected nondeterministically.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> FaultEffects
		{
			get { return _faultEffects; }
		}

		/// <summary>
		///     Gets the method behavior that is invoked when the current one is inactive.
		/// </summary>
		public MethodBehavior FallbackBehavior { get; private set; }

		/// <summary>
		///     Gets the priority overrides that can be used to (partially or fully) override the nondeterministic selection
		///     of fault effects.
		/// </summary>
		public int[] PriorityOverrides { get; private set; }

		/// <summary>
		///     Resets the <see cref="PriorityOverrides" /> property to its initial value.
		/// </summary>
		public void ResetPriorityOverrides()
		{
			for (var i = 0; i < _faultEffects.Length; ++i)
				PriorityOverrides[i] = _faultEffects[i].Priority;
		}

		/// <summary>
		///     Gets a value indicating whether the fallback behavior should be used. This is the case when the fault the injected fault
		///     effect belongs to is currently not occurring.
		/// </summary>
		[UsedImplicitly]
		private int ChooseCase()
		{
			_enabledFaultEffects.Clear();

			// Determine the enabled fault effects
			for (var i = 0; i < _faultEffects.Length; ++i)
			{
				if (_faultEffects[i].DeclaringFault.Fault.IsOccurring)
					_enabledFaultEffects.Add(i);
			}

			// If there are no faults occurring, invoke the fallback behavior
			if (_enabledFaultEffects.Count == 0)
				return _faultEffects.Length;

			// If there is only one active fault effect, invoke it
			if (_enabledFaultEffects.Count == 1)
				return _enabledFaultEffects[0];

			// Remove all enabled fault effects whose dynamic priority is too low
			var maxPriority = _enabledFaultEffects.Select(faultEffect => PriorityOverrides[faultEffect]).Max();
			for (var i = 0; i < _enabledFaultEffects.Count; ++i)
			{
				if (PriorityOverrides[_enabledFaultEffects[i]] < maxPriority)
					_enabledFaultEffects.RemoveAt(i--);
			}

			// If we've now ruled out all nondeterminism, invoke the fault effect with the highest dynamic priority
			if (_enabledFaultEffects.Count == 1)
				return _enabledFaultEffects[0];

			// Otherwise, nondeterministically choose one of the fault effects
			return _enabledFaultEffects[_random.Next(0, _enabledFaultEffects.Count)];
		}

		/// <summary>
		///     Binds the method behavior, using the <paramref name="fallbackBehavior" /> when the current behavior is inactive.
		/// </summary>
		/// <param name="fallbackBehavior">The fallback behavior that should be invoked when the current behavior is inactive.</param>
		/// <param name="delegateType">The delegate type representing the signature of the method.</param>
		internal override void Bind(MethodBehavior fallbackBehavior, Type delegateType)
		{
			Requires.NotNull(fallbackBehavior, () => fallbackBehavior);
			Requires.NotNull(delegateType, () => delegateType);

			FallbackBehavior = fallbackBehavior;

			// We now dynamically generate and compile the following method:
			// -------------------------------------------------------------
			// ret M(params) 
			// {
			//     switch (ChooseCase())
			//     {
			//         case 0: return FaultEffects[0](params);
			//         case 1: return FaultEffects[1](params);
			//			  ...
			//         case n: return FaultEffects[n](params);
			//         default: return FallbackBehavior(params);
			//     }
			// }
			// -------------------------------------------------------------

			// Inputs to the generated method
			var parameters = Method.MethodInfo.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
			var methodBehavior = Expression.Constant(this);
			var fallbackDelegate = Expression.Constant(fallbackBehavior.Delegate, Method.MethodType);
			var faultEffectDelegates = FaultEffects.Select(faultEffect => Expression.Constant(faultEffect.CreateDelegate(delegateType)));

			// Invocations
			var chooseCaseInvocation = Expression.Call(methodBehavior, "ChooseCase", Type.EmptyTypes);
			var invokeFallback = Expression.Invoke(fallbackDelegate, parameters);
			var invokeFaultEffects = faultEffectDelegates.Select(faultEffectDelegate => Expression.Invoke(faultEffectDelegate, parameters));

			// Switch statement
			var cases = invokeFaultEffects.Select((invocation, index) => Expression.SwitchCase(invocation, Expression.Constant(index)));
			var switchStatement = Expression.Switch(chooseCaseInvocation, invokeFallback, cases.ToArray());

			// Create and compile the method and bind the resulting delegate
			var lambda = Expression.Lambda(Method.MethodType, switchStatement, parameters);
			BindDelegate(lambda.Compile());
		}
	}
}