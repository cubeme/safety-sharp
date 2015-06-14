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
	using System.Reflection;
	using CompilerServices;
	using Utilities;

	/// <summary>
	///     Represents a base class for the immutable metadata of all method-based members of a S#
	///     <see cref="Component" /> instance.
	/// </summary>
	public abstract class ComponentMethodInfo
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the method belongs to.</param>
		/// <param name="method">The method that represents the component method.</param>
		/// <param name="baseMethod">The overridden base method, if any.</param>
		internal ComponentMethodInfo(ComponentInfo component, MethodInfo method, MethodInfo baseMethod = null)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(method, () => method);

			Component = component;
			Method = method;
			BaseMethod = baseMethod;

			var backingFieldAttribute = method.GetCustomAttribute<BackingFieldAttribute>();
			Requires.That(backingFieldAttribute != null, "Expected to find an instance of '{0}' on component member '{1}'.",
				typeof(BackingFieldAttribute).FullName, method);

			BackingField = backingFieldAttribute.GetFieldInfo(method.DeclaringType);
		}

		/// <summary>
		///     Gets the backing field that stores the runtime implementation of the method. The runtime implementation can potentially
		///     be affected by component faults.
		/// </summary>
		public FieldInfo BackingField { get; private set; }

		/// <summary>
		///     Gets the underlying method.
		/// </summary>
		public MethodInfo Method { get; private set; }

		/// <summary>
		///     Gets the overridden base method, if any.
		/// </summary>
		public MethodInfo BaseMethod { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the method overrides a method of a base class.
		/// </summary>
		public bool IsOverride
		{
			get { return BaseMethod != null; }
		}

		/// <summary>
		///     Gets the name of the method.
		/// </summary>
		public string Name
		{
			get { return Method.Name; }
		}

		/// <summary>
		///     Gets the component the field belongs to.
		/// </summary>
		public ComponentInfo Component { get; private set; }
	}
}