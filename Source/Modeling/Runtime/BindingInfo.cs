﻿// The MIT License (MIT)
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
	using System.Reflection;
	using CompilerServices;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a binding between two ports.
	/// </summary>
	public class BindingInfo
	{
		/// <summary>
		///     The component the binding belongs to.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     The provided port of the binding.
		/// </summary>
		private readonly Delegate _providedPort;

		/// <summary>
		///     The required port of the binding.
		/// </summary>
		private readonly Delegate _requiredPort;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component that declares the binding.</param>
		/// <param name="requiredPort">The target port of the port binding.</param>
		/// <param name="providedPort">The source port of the port binding.</param>
		internal BindingInfo(Component component, Delegate requiredPort, Delegate providedPort)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(requiredPort, () => requiredPort);
			Requires.NotNull(providedPort, () => providedPort);

			_component = component;
			_requiredPort = requiredPort;
			_providedPort = providedPort;

			// We initialize the required port's backing field now instead of waiting until the entire component hierarchy 
			// metadata is initialized; this basically allows the user to call required ports as soon as their bindings
			// have been established.
			var backingField = requiredPort.Method.GetCustomAttribute<BackingFieldAttribute>();
			Requires.That(backingField != null, () => requiredPort,
				"Expected to find an instance of '{0}' on the required port.", typeof(BackingFieldAttribute).FullName);

			var field = backingField.GetFieldInfo(requiredPort.Method.DeclaringType);
			Requires.That(field.GetValue(requiredPort.Target) == null, () => requiredPort, "The required port has already been bound.");

			var adaptedDelegate = Delegate.CreateDelegate(field.FieldType, providedPort.Target, providedPort.Method);
			field.SetValue(requiredPort.Target, adaptedDelegate);
		}

		/// <summary>
		///     Gets the metadata of the component the binding belongs to.
		/// </summary>
		public ComponentInfo Component
		{
			get { return _component.GetComponentInfo(); }
		}

		/// <summary>
		///     Gets the metadata of the bound provided port.
		/// </summary>
		public ProvidedPortInfo ProvidedPort
		{
			get { return ((Component)_providedPort.Target).GetComponentInfo().ProvidedPorts.Single(port => port.Method == _providedPort.Method); }
		}

		/// <summary>
		///     Gets the metadata of the bound required port.
		/// </summary>
		public RequiredPortInfo RequiredPort
		{
			get { return ((Component)_requiredPort.Target).GetComponentInfo().RequiredPorts.Single(port => port.Method == _requiredPort.Method); }
		}
	}
}