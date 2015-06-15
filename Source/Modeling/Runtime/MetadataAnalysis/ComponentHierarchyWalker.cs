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
	using Utilities;

	/// <summary>
	///     Analyzes a component hierarchy.
	/// </summary>
	internal abstract class ComponentHierarchyWalker
	{
		/// <summary>
		///     The root of the component hierarchy.
		/// </summary>
		private readonly ComponentInfo _root;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="root">The root of the component hierarchy.</param>
		protected ComponentHierarchyWalker(ComponentInfo root)
		{
			Requires.NotNull(root, () => root);
			_root = root;
		}

		/// <summary>
		///     Walks the component hierarchy in pre-order.
		/// </summary>
		internal void WalkPreOrder()
		{
			Action<ComponentInfo> preOrder = null;
			preOrder = component =>
			{
				Visit(component);

				foreach (var subcomponent in component.Subcomponents)
					preOrder(subcomponent);
			};

			preOrder(_root);
		}

		/// <summary>
		///     Visits the <paramref name="componentInfo" />.
		/// </summary>
		/// <param name="componentInfo">The component metadata that should be visited.</param>
		protected abstract void Visit(ComponentInfo componentInfo);
	}
}