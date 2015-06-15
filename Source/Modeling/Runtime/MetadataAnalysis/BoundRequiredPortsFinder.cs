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
	///     Walks the component hierarchy looking for the required ports that are bound to a provided port.
	/// </summary>
	internal class BoundRequiredPortsFinder : ComponentHierarchyWalker
	{
		/// <summary>
		///     The provided port the required ports are retrieved for.
		/// </summary>
		private readonly ProvidedPortMetadata _providedPort;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="root">The root of the component hierarchy.</param>
		/// <param name="providedPort">The provided port the required ports should be retrieved for.</param>
		public BoundRequiredPortsFinder(ComponentMetadata root, ProvidedPortMetadata providedPort)
			: base(root)
		{
			Requires.NotNull(providedPort, () => providedPort);

			RequiredPorts = new List<RequiredPortMetadata>();
			_providedPort = providedPort;
		}

		/// <summary>
		///     Gets the required ports that are bound to the provided port.
		/// </summary>
		public List<RequiredPortMetadata> RequiredPorts { get; private set; }

		/// <summary>
		///     Visits the <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The component metadata that should be visited.</param>
		protected override void Visit(ComponentMetadata metadata)
		{
			RequiredPorts.AddRange(from binding in metadata.Bindings
								   where binding.ProvidedPort == _providedPort
								   select binding.RequiredPort);
		}
	}
}