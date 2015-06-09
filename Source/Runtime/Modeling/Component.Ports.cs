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

namespace SafetySharp.Runtime.Modeling
{
	using System;
	using System.Diagnostics;
	using System.Linq;
	using System.Reflection;
	using CompilerServices;
	using Utilities;

	partial class Component
	{
		/// <summary>
		///     Gets all required ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic RequiredPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
		}

		/// <summary>
		///     Gets all provided ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic ProvidedPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
		}

		/// <summary>
		///     Initializes all provided ports of the component by assigning the ports' non-faulty implementations to the ports'
		///     delegate fields.
		/// </summary>
		private void InitializeProvidedPorts()
		{
			var providedPorts = GetType()
				.GetMethods(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
				.Where(m => m.GetCustomAttribute<ProvidedAttribute>() != null && !m.IsAbstract);

			foreach (var port in providedPorts)
			{
				var backingField = port.GetCustomAttribute<BackingFieldAttribute>();
				Requires.That(backingField != null, "Expected to find an instance of '{0}' on provided port '{1}'.",
					typeof(BackingFieldAttribute).FullName, port);

				var behavior = port.GetCustomAttribute<PortBehaviorAttribute>();
				Requires.That(behavior != null, "Expected to find an instance of '{0}' on provided port '{1}'.",
					typeof(PortBehaviorAttribute).FullName, port);

				var field = backingField.GetFieldInfo(port.DeclaringType);
				var flags = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
				var parameters = port.GetParameters().Select(p => p.ParameterType).ToArray();
				var implementation = port.DeclaringType.GetMethod(behavior.MethodName, flags, null, parameters, null);
				Requires.That(implementation != null, "Unable to find behavior of provided port '{0}'.", port);

				var implementationDelegate = Delegate.CreateDelegate(field.FieldType, this, implementation);
				field.SetValue(this, implementationDelegate);
			}
		}
	}
}