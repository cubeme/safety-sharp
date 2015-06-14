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
	using Utilities;

	/// <summary>
	///     Represents a binding between two ports.
	/// </summary>
	public class BindingInfo
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component that declares the binding.</param>
		/// <param name="targetPort">The target port of the port binding.</param>
		/// <param name="sourcePort">The source port of the port binding.</param>
		internal BindingInfo(ComponentInfo component, Delegate targetPort, Delegate sourcePort)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(targetPort, () => targetPort);
			Requires.NotNull(sourcePort, () => sourcePort);

			Component = component;
			TargetPort = targetPort;
			SourcePort = sourcePort;
		}

		/// <summary>
		///     Gets the component the binding belongs to.
		/// </summary>
		public ComponentInfo Component { get; private set; }

		/// <summary>
		///     Gets the target port of the binding.
		/// </summary>
		public Delegate TargetPort { get; private set; }

		/// <summary>
		///     Gets the source port of the binding.
		/// </summary>
		public Delegate SourcePort { get; private set; }
	}
}