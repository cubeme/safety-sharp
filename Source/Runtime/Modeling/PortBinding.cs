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
	using System.Reflection;
	using CompilerServices;
	using Utilities;

	/// <summary>
	///     Represents a binding of two ports. Use the syntax <c>component1.RequiredPorts.Port = component2.ProvidedPorts.Port</c>
	///     to instantiate a binding.
	/// </summary>
	public sealed class PortBinding
	{
		/// <summary>
		///     Indicates whether the binding has been sealed an no future modifications are possible.
		/// </summary>
		private bool _isSealed;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="targetPort">The target port of the port binding.</param>
		/// <param name="sourcePort">The source port of the port binding.</param>
		public PortBinding(PortInfo targetPort, PortInfo sourcePort)
		{
			Requires.NotNull(targetPort, () => targetPort);
			Requires.NotNull(sourcePort, () => sourcePort);

			TargetPort = targetPort;
			SourcePort = sourcePort;
			Kind = BindingKind.Instantaneous;
		}

		/// <summary>
		///     Gets the source port of the binding.
		/// </summary>
		internal PortInfo SourcePort { get; private set; }

		/// <summary>
		///     Gets the target port of the binding.
		/// </summary>
		internal PortInfo TargetPort { get; private set; }

		/// <summary>
		///     Gets or sets the kind of the binding.
		/// </summary>
		internal BindingKind Kind { get; set; }

		/// <summary>
		///     Gets or sets the object that instantiated the binding.
		/// </summary>
		internal object Binder { get; set; }

		/// <summary>
		///     Gets the user-friendly name of the binder.
		/// </summary>
		internal string BinderName
		{
			get
			{
				var component = Binder as Component;
				if (component != null)
					return component.UnmangledName;

				var model = Binder as Model;
				if (model != null)
					return "Model";

				return "<unknown>";
			}
		}

		/// Finalizes the bindings's metadata, disallowing any future metadata modifications.
		internal void FinalizeMetadata()
		{
			if (_isSealed)
				return;

			_isSealed = true;

			var backingField = TargetPort.Method.GetCustomAttribute<BackingFieldAttribute>();
			Requires.That(backingField != null, "Expected to find an instance of '{0}' on the target port.", typeof(BackingFieldAttribute).FullName);

			var field = backingField.GetFieldInfo(TargetPort.Method.DeclaringType);
			var adaptedDelegate = Delegate.CreateDelegate(field.FieldType, SourcePort.Component, SourcePort.Method);
			field.SetValue(TargetPort.Component, adaptedDelegate);
		}

		/// <summary>
		///     Changes the kind of the binding to delayed, meaning that the invocation of the bound port is delayed by one system step.
		/// </summary>
		public void Delayed()
		{
			Requires.That(!_isSealed, "Modifications of the port binding's metadata are only allowed during model initialization.");
			Kind = BindingKind.Delayed;
		}
	}
}