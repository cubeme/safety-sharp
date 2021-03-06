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
	using System.Diagnostics;
	using System.Linq;
	using System.Reflection;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the the immutable metadata of a provided port of a S# <see cref="Component" />.
	/// </summary>
	public sealed class ProvidedPortMetadata : MethodMetadata
	{
		/// <summary>
		///     The metadata of the bindings affecting the port.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private readonly Lazy<IEnumerable<BindingMetadata>> _bindings;

		/// <summary>
		///     The metadata of the required ports that have been bound to the provided port.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private readonly Lazy<IEnumerable<RequiredPortMetadata>> _boundRequiredPorts;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the method belongs to.</param>
		/// <param name="port">The CLR method representing the component's port.</param>
		/// <param name="name">The name of the port; if <c>null</c>, the port's CLR name is used.</param>
		/// <param name="basePort">The overridden base port, if any.</param>
		public ProvidedPortMetadata(Component component, MethodInfo port, string name = null, MethodMetadata basePort = null)
			: base(component, port, name, basePort)
		{
			Requires.That(HasImplementation, () => port, "Provided ports must have an implementation.");
			Requires.That(CanBeAffectedByFaultEffects, () => port, "Provided ports must be sensitive to fault effects.");

			_boundRequiredPorts = new Lazy<IEnumerable<RequiredPortMetadata>>(() => Bindings.Select(binding => binding.RequiredPort));
			_bindings = new Lazy<IEnumerable<BindingMetadata>>(() =>
			{
				var bindings = new List<BindingMetadata>();

				DeclaringObject.RootComponent.VisitPreOrder(
					metadata => bindings.AddRange(metadata.Bindings.Where(binding => binding.ProvidedPort == this)));

				return bindings;
			});
		}

		/// <summary>
		///     Gets the metadata of the declaring component.
		/// </summary>
		public new ComponentMetadata DeclaringObject
		{
			get { return ((ComponentMetadata)base.DeclaringObject); }
		}

		/// <summary>
		///     Gets the metadata of the required ports that have been bound to the provided port.
		/// </summary>
		public IEnumerable<RequiredPortMetadata> BoundRequiredPorts
		{
			get { return _boundRequiredPorts.Value; }
		}

		/// <summary>
		///     Gets the metadata of the bindings affecting the port.
		/// </summary>
		public IEnumerable<BindingMetadata> Bindings
		{
			get { return _bindings.Value; }
		}
	}
}