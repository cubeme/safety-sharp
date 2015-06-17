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

	/// <summary>
	///     Collects the metadata of all components found within the component hierarchy. Throws a
	///     <see cref="ComponentHierarchyException" /> if a component is encountered in multiple locations of
	///     the component hierarchy.
	/// </summary>
	internal sealed class ComponentCollector : ComponentHierarchyWalker
	{
		private readonly HashSet<ComponentMetadata> _components = new HashSet<ComponentMetadata>();

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="root">The root of the component hierarchy.</param>
		public ComponentCollector(ComponentMetadata root)
			: base(root)
		{
		}

		/// <summary>
		///     Gets the metadata of all components within the component hierarchy.
		/// </summary>
		public IEnumerable<ComponentMetadata> Components
		{
			get { return _components; }
		}

		/// <summary>
		///     Visits the <paramref name="metadata" />.
		/// </summary>
		/// <param name="metadata">The component metadata that should be visited.</param>
		protected override void Visit(ComponentMetadata metadata)
		{
			if (!_components.Add(metadata))
				throw new ComponentHierarchyException(metadata);
		}
	}
}