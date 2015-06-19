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
	///     Represents a deterministic fault effect that is injected and executed deterministically.
	/// </summary>
	public sealed class DeterministicFaultInjection : FaultInjection
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the fault injection belongs to.</param>
		/// <param name="faultEffect">The fault effect that should be injected deterministically.</param>
		public DeterministicFaultInjection(object obj, MethodMetadata method, FaultEffectMetadata faultEffect)
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
		///     Gets a value indicating whether the fallback behavior should be used. This is the case when the fault the injected fault
		///     effect belongs to is currently not occurring.
		/// </summary>
		[UsedImplicitly]
		private bool UseFallbackBehavior
		{
			// If the method is already being executed, we have to forward to the fallback behavior to avoid stack overflows
			get { return IsRunning || !FaultEffect.DeclaringFault.Fault.IsOccurring; }
		}

		/// <summary>
		///     Binds the fault injection, using the <paramref name="fallbackBehavior" /> when the fault injection is inactive.
		/// </summary>
		/// <param name="fallbackBehavior">The fallback behavior that should be invoked when the fault injection is inactive.</param>
		/// <param name="delegateType">The delegate type representing the signature of the method.</param>
		internal override void Bind(Delegate fallbackBehavior, Type delegateType)
		{
			// Ideally, we would also check that fallbackBehavior != null; however, that would require all tests to 
			// bind all required ports, which would be too cumbersome to endure; hence, we go without the null check here
			Requires.NotNull(delegateType, () => delegateType);

			// We now dynamically generate and compile the following method:
			// -------------------------------------------------------------
			// ret M(params) 
			// {
			//     try
			//     {
			//         var useFallback = this.UseFallbackBehavior();
			//         this.IsRunning = true;
			//	       if (useFallback)
			//	           return this.FallbackBehavior(params);
			//	       else
			//	           return this.FaultEffect(params);
			//     }
			//     finally 
			//     {
			//          this.IsRunning = false;
			//     }
			// }
			// -------------------------------------------------------------

			// Inputs to the generated method
			var parameters = Method.MethodInfo.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
			var methodBehavior = Expression.Constant(this);
			var fallbackDelegate = Expression.Constant(fallbackBehavior, Method.MethodType);
			var faultEffectDelegate = Expression.Constant(FaultEffect.CreateDelegate(delegateType));
			var localVariable = Expression.Parameter(typeof(bool));

			// IsRunning updates
			var isRunningProperty = Expression.Property(methodBehavior, "IsRunning");
			var setIsRunningTrue = Expression.Assign(isRunningProperty, Expression.Constant(true));
			var setIsRunningFalse = Expression.Assign(isRunningProperty, Expression.Constant(false));

			// Invocations
			var useFallback = Expression.Assign(localVariable, Expression.Property(methodBehavior, "UseFallbackBehavior"));
			var invokeFallback = Expression.Invoke(fallbackDelegate, parameters);
			var invokeFaultEffect = Expression.Invoke(faultEffectDelegate, parameters);

			// Try block
			var conditional = Expression.Condition(localVariable, invokeFallback, invokeFaultEffect);
			var tryBlock = Expression.Block(new[] { localVariable }, useFallback, setIsRunningTrue, conditional);

			// Try-finally statement
			var tryFinally = Expression.TryFinally(tryBlock, setIsRunningFalse);

			// Create and compile the method and bind the resulting delegate
			var lambda = Expression.Lambda(Method.MethodType, tryFinally, parameters);
			BindDelegate(lambda.Compile());
		}
	}
}