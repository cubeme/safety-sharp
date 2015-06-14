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
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the the immutable metadata of a behavior of a S# <see cref="Component" />.
	/// </summary>
	public abstract class BehaviorInfo : ComponentMethodInfo
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the method belongs to.</param>
		/// <param name="behavior">The method representing the component's behavior.</param>
		/// <param name="baseBehavior">The overridden behavior of the base type, if any.</param>
		internal BehaviorInfo(Component component, MethodInfo behavior, MethodInfo baseBehavior = null)
			: base(component, behavior, baseBehavior)
		{
			var behaviorAttribute = behavior.GetCustomAttribute<MethodBehaviorAttribute>();
			Requires.That(behaviorAttribute != null, "Expected to find an instance of '{0}' on component member '{1}'.",
				typeof(MethodBehaviorAttribute).FullName, behavior);

			ImplementationMethod = behaviorAttribute.GetMethodInfo(behavior.DeclaringType);

			var implementationDelegate = Delegate.CreateDelegate(BackingField.FieldType, component, ImplementationMethod);
			BackingField.SetValue(component, implementationDelegate);
		}

		/// <summary>
		///     Gets the method that represents the behavior's default implementation in the absence of any component faults.
		/// </summary>
		public MethodInfo ImplementationMethod { get; private set; }
	}
}