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

namespace SafetySharp.Runtime.MetadataAnalysis
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Utilities;

	/// <summary>
	///     Walks the component hierarchy looking for the provided ports that are bound to a required port.
	/// </summary>
	internal class BoundProvidedPortsFinder : ComponentHierarchyWalker
	{
		/// <summary>
		///     The required port the provided ports are retrieved for.
		/// </summary>
		private readonly RequiredPortInfo _requiredPort;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="root">The root of the component hierarchy.</param>
		/// <param name="requiredPort">The required port the provided ports should be retrieved for.</param>
		public BoundProvidedPortsFinder(ComponentInfo root, RequiredPortInfo requiredPort)
			: base(root)
		{
			Requires.NotNull(requiredPort, () => requiredPort);

			ProvidedPorts = new List<ProvidedPortInfo>();
			_requiredPort = requiredPort;
		}

		/// <summary>
		///     Gets the provided ports that are bound to the required port.
		/// </summary>
		public List<ProvidedPortInfo> ProvidedPorts { get; private set; }

		/// <summary>
		///     Visits the <paramref name="componentInfo" />.
		/// </summary>
		/// <param name="componentInfo">The component metadata that should be visited.</param>
		protected override void Visit(ComponentInfo componentInfo)
		{
			ProvidedPorts.AddRange(from binding in componentInfo.Bindings
								   where binding.RequiredPort == _requiredPort
								   select binding.ProvidedPort);
		}
	}
}