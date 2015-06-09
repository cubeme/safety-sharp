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
	using Utilities;

	/// <summary>
	///     Provides metadata about a port.
	/// </summary>
	public sealed class PortInfo
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component that declares the port.</param>
		/// <param name="method">The method representing the port.</param>
		internal PortInfo(IComponent component, MethodInfo method)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(method, () => method);

			Component = component;
			Method = method;
		}

		/// <summary>
		///     Gets the method representing the port.
		/// </summary>
		internal MethodInfo Method { get; private set; }

		/// <summary>
		///     Gets the component instance that declares the port.
		/// </summary>
		internal IComponent Component { get; private set; }

		/// <summary>
		///     Gets a value indicating whether the port is a required port.
		/// </summary>
		internal bool IsRequiredPort
		{
			get { return Method.HasAttribute<RequiredAttribute>(); }
		}

		/// <summary>
		///     Creates a new instance for a method port.
		/// </summary>
		/// <param name="port">The delegate that represents the port.</param>
		public static PortInfo MethodPort(Delegate port)
		{
			Requires.NotNull(port, () => port);
			Requires.OfType<IComponent>(port.Target, () => port,
				"Expected a port declared by a type implementing '{0}'.", typeof(IComponent).FullName);

			return new PortInfo((IComponent)port.Target, port.Method);
		}
	}
}