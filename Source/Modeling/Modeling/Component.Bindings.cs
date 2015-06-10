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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Diagnostics;
	using Utilities;

	partial class Component
	{
		/// <summary>
		///     The component's port bindings during initialization.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private readonly List<PortBinding> _bindings = new List<PortBinding>();

		/// <summary>
		///     The component's initialized port bindings.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private ImmutableArray<PortBinding> _initializedBindings;

		/// <summary>
		///     Gets the port bindings of the component.
		/// </summary>
		internal ImmutableArray<PortBinding> Bindings
		{
			get
			{
				RequiresIsSealed();
				return _initializedBindings;
			}
		}

		/// <summary>
		///     Adds the <paramref name="portBinding" /> to the component's bindings.
		/// </summary>
		/// <param name="portBinding">The port binding that should be added.</param>
		protected PortBinding Bind(PortBinding portBinding)
		{
			Requires.NotNull(portBinding, () => portBinding);

			portBinding.Binder = this;
			_bindings.Add(portBinding);

			return portBinding;
		}

		/// <summary>
		///     Initializes the bindings of the component.
		/// </summary>
		private void InitializeBindings()
		{
			_initializedBindings = _bindings.ToImmutableArray();

			foreach (var binding in _bindings)
				binding.FinalizeMetadata();
		}
	}
}