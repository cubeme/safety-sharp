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
	using Utilities;

	/// <summary>
	///     Represents a nondeterministic set of fault effects that selects and executes one effect nondeterministically instead of
	///     the fallback behavior when one or more of its corresponding faults are active.
	/// </summary>
	public sealed class NondeterministicFaultBehavior : MethodBehavior
	{
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
			FaultEffects = faultEffects;
		}

		/// <summary>
		///     Gets the metadata of the fault effects that are injected nondeterministically.
		/// </summary>
		public IEnumerable<FaultEffectMetadata> FaultEffects { get; private set; }

		/// <summary>
		///     Gets the method behavior that is invoked when the current one is inactive.
		/// </summary>
		public MethodBehavior FallbackBehavior { get; private set; }

		/// <summary>
		///     Binds the method behavior, using the <paramref name="fallbackBehavior" /> when the current behavior is inactive.
		/// </summary>
		/// <param name="fallbackBehavior">The fallback behavior that should be invoked when the current behavior is inactive.</param>
		/// <param name="delegateType">The delegate type representing the signature of the method.</param>
		internal override void Bind(MethodBehavior fallbackBehavior, Type delegateType)
		{
			Requires.NotNull(fallbackBehavior, () => fallbackBehavior);

			FallbackBehavior = fallbackBehavior;
		}
	}
}