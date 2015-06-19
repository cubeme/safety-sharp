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
	public sealed class IntendedBehavior
	{
		/// <summary>
		///     The object the method belongs to.
		/// </summary>
		private readonly object _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The S# object the method belongs to.</param>
		/// <param name="method">The metadata of the method the behavior belongs to.</param>
		public IntendedBehavior(object obj, MethodMetadata method)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(method, () => method);

			Method = method;
			_object = obj;
		}

		/// <summary>
		///     Gets the metadata of the method the behavior belongs to.
		/// </summary>
		public MethodMetadata Method { get; private set; }

		/// <summary>
		///     Gets the delegate that has been bound as the intended behavior.
		/// </summary>
		internal Delegate Delegate { get; private set; }

		/// <summary>
		///     Binds the intended method behavior.
		/// </summary>
		internal void Bind()
		{
			// Set the intended behavior - if the method doesn't have an implementation, the intended behavior
			// is expected to be set by someone else
			if (!Method.HasImplementation)
				return;

			// If the method cannot be affected by faults, the intended behavior is the method itself
			if (!Method.CanBeAffectedByFaultEffects)
				return;

			Delegate = Delegate.CreateDelegate(Method.BackingField.FieldType, _object, Method.IntendedBehavior);
			Method.BackingField.SetValue(_object, Delegate);
		}

		/// <summary>
		///     Binds the externally provided intended behavior of the method.
		/// </summary>
		internal void BindExternal()
		{
			if (Method.HasImplementation)
				return;

			// We allow the external behavior to be null to simplify testing (otherwise all required ports
			// would have to be bound in all tests). We'll detect unbound required ports later
			var externalBehavior = Method.BackingField.GetValue(_object) as Delegate;
			if (externalBehavior != null)
				Delegate = externalBehavior;
		}
	}
}