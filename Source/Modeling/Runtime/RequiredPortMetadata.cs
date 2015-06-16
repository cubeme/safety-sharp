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
	using System.Reflection;
	using MetadataAnalysis;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the the immutable metadata of a required port of a S# <see cref="Component" />.
	/// </summary>
	public sealed class RequiredPortMetadata : MethodMetadata
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the method belongs to.</param>
		/// <param name="port">The CLR method representing the component's port.</param>
		internal RequiredPortMetadata(Component component, MethodInfo port)
			: base(component, port)
		{
			Requires.That(!HasImplementation, () => port, "Requires ports must not have an implementation.");
			Requires.That(CanBeAffectedByFaultEffects, () => port, "Required ports must be sensitive to fault effects.");
		}

		/// <summary>
		///     Gets the metadata of the provided ports that have been bound to the required port.
		/// </summary>
		public IEnumerable<ProvidedPortMetadata> BoundProvidedPorts
		{
			get
			{
				var finder = new BoundProvidedPortsFinder(((ComponentMetadata)DeclaringObject).RootComponent, this);
				finder.WalkPreOrder();
				return finder.ProvidedPorts;
			}
		}
	}
}