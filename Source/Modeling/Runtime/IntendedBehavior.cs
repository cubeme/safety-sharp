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
	using Utilities;

	/// <summary>
	///     Represents the intended behavior of a method, disregarding any faults.
	/// </summary>
	public sealed class IntendedBehavior : MethodBehavior
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the behavior belongs to.</param>
		public IntendedBehavior(object obj, MethodMetadata method)
			: base(obj, method)
		{
		}

		/// <summary>
		///     Binds the intended method behavior. The <paramref name="fallbackBehavior" /> must be <c>null</c> as the intended
		///     behavior can always be executed and never falls back to another behavior.
		/// </summary>
		/// <param name="fallbackBehavior">The fallback behavior that should be invoked when the current behavior is inactive.</param>
		/// <param name="delegateType">The delegate type representing the signature of the method.</param>
		internal override void Bind(MethodBehavior fallbackBehavior, Type delegateType)
		{
			Requires.That(fallbackBehavior == null, () => fallbackBehavior, "The fallback behavior is never invoked.");

			// Set the intended behavior - if the method doesn't have an implementation, the intended behavior
			// is expected to be set by someone else
			if (Method.HasImplementation)
				BindDelegate(Delegate.CreateDelegate(Method.BackingField.FieldType, Object, Method.IntendedBehavior));
		}
	}
}