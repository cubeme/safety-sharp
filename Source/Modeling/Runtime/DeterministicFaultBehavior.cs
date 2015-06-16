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
	using System.Linq.Expressions;
	using JetBrains.Annotations;
	using Utilities;

	/// <summary>
	///     Represents a deterministic fault effect that is executed deterministically instead of the fallback behavior when
	///     the corresponding fault is active.
	/// </summary>
	public sealed class DeterministicFaultBehavior : MethodBehavior
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the behavior belongs to.</param>
		/// <param name="faultEffect">The fault effect that should be injected deterministically.</param>
		public DeterministicFaultBehavior(object obj, MethodMetadata method, FaultEffectMetadata faultEffect)
			: base(obj, method)
		{
			Requires.NotNull(faultEffect, () => faultEffect);
			FaultEffect = faultEffect;
		}

		/// <summary>
		///     Gets the metadata of the fault effect that is injected deterministically.
		/// </summary>
		public FaultEffectMetadata FaultEffect { get; private set; }

		/// <summary>
		///     Gets the method behavior that is invoked when the current one is inactive.
		/// </summary>
		public MethodBehavior FallbackBehavior { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the fallback behavior should be used. This is the case when the fault the injected fault
		///     effect belongs to is currently not occurring.
		/// </summary>
		[UsedImplicitly]
		private bool UseFallbackBehavior
		{
			get { return !FaultEffect.DeclaringFault.Fault.IsOccurring; }
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
			//     if (this.UseFallbackBehavior())
			//         return fallbackBehavior(params);
			//     else
			//         return faultEffect(params);
			// }
			// -------------------------------------------------------------

			// Inputs to the generated method
			var parameters = Method.MethodInfo.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
			var methodBehavior = Expression.Constant(this);
			var fallbackDelegate = Expression.Constant(fallbackBehavior.Delegate, Method.MethodType);
			var faultEffectDelegate = Expression.Constant(FaultEffect.CreateDelegate(delegateType));

			// Invocations
			var useFallback = Expression.Property(methodBehavior, "UseFallbackBehavior");
			var invokeFallback = Expression.Invoke(fallbackDelegate, parameters);
			var invokeFaultEffect = Expression.Invoke(faultEffectDelegate, parameters);

			// Conditional
			var conditional = Expression.Condition(useFallback, invokeFallback, invokeFaultEffect);

			// Create and compile the method and bind the resulting delegate
			var lambda = Expression.Lambda(Method.MethodType, conditional, parameters);
			BindDelegate(lambda.Compile());
		}
	}
}