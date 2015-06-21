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
	using JetBrains.Annotations;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a base class for fault injections of a method.
	/// </summary>
	public abstract class FaultInjection
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the behavior belongs to.</param>
		internal FaultInjection(IMetadataObject obj, MethodMetadata method)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(method, () => method);

			Method = method;
			Object = obj;
		}

		/// <summary>
		///     Gets the object the <see cref="Method" /> belongs to.
		/// </summary>
		public IMetadataObject Object { get; private set; }

		/// <summary>
		///     Gets or sets a value indicating whether the method is currently being executed.
		/// </summary>
		[UsedImplicitly]
		protected bool IsRunning { get; set; }

		/// <summary>
		///     Gets a value indicating whether the fault injection is deterministic or whether a fault effect is choosen
		///     nondeterministically from a set of enabled ones.
		/// </summary>
		public bool IsDeterministic
		{
			get { return this is DeterministicFaultInjection; }
		}

		/// <summary>
		///     Gets the metadata of the method the fault injection belongs to.
		/// </summary>
		public MethodMetadata Method { get; private set; }

		/// <summary>
		///     Gets the delegate that has been bound by the fault injection.
		/// </summary>
		internal Delegate Delegate { get; private set; }

		/// <summary>
		///     Binds the fault injection, using the <paramref name="fallbackBehavior" /> when the fault injection is inactive.
		/// </summary>
		/// <param name="fallbackBehavior">The fallback behavior that should be invoked when the fault injection is inactive.</param>
		/// <param name="delegateType">The delegate type representing the signature of the method.</param>
		internal abstract void Bind(Delegate fallbackBehavior, Type delegateType);

		/// <summary>
		///     Binds the <paramref name="behaviorDelegate" /> to the method's backing field.
		/// </summary>
		protected void BindDelegate(Delegate behaviorDelegate)
		{
			Requires.NotNull(behaviorDelegate, () => behaviorDelegate);

			Delegate = behaviorDelegate;
			Method.BackingField.SetValue(Object, behaviorDelegate);
		}
	}
}