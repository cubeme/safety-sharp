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

namespace SafetySharp.Runtime.MetadataAnalyzers
{
	using System;
	using Utilities;

	/// <summary>
	///     Raised when a component is found in multiple locations of a component hierarchy.
	/// </summary>
	public class InvalidHierarchyStructureException : Exception
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The metadata of the component that was found in multiple locations of a component hierarchy.</param>
		internal InvalidHierarchyStructureException(ComponentMetadata component)
			: base("A component has been found in multiple locations of the component hierarchy; " +
				   "the 'Component' property contains the metadata of the component that violated the hierarchy constraint.")
		{
			Requires.NotNull(component, () => component);
			Component = component;
		}

		/// <summary>
		///     Gets the metadata of the component that was found in multiple locations of a component hierarchy.
		/// </summary>
		public ComponentMetadata Component { get; private set; }
	}
}