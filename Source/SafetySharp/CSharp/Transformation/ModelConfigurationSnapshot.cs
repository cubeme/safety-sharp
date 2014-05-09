// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using Modeling;

	/// <summary>
	///     During model transformation, a <see cref="ModelConfigurationSnapshot" /> instance stores an immutable snapshot of the
	///     mutable state of a <see cref="ModelConfiguration" /> instance.
	/// </summary>
	internal class ModelConfigurationSnapshot
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="ModelConfigurationSnapshot" /> type.
		/// </summary>
		/// <param name="partitionRoots">The partition root <see cref="ComponentSnapshot" /> instances of the configuration.</param>
		internal ModelConfigurationSnapshot(ImmutableArray<ComponentSnapshot> partitionRoots)
		{
			PartitionRoots = partitionRoots;
			Components = partitionRoots.SelectMany(GetAllComponents).ToImmutableArray();
		}

		/// <summary>
		///     Gets the partition root <see cref="ComponentSnapshot" /> instances of the configuration.
		/// </summary>
		internal ImmutableArray<ComponentSnapshot> PartitionRoots { get; private set; }

		/// <summary>
		///     Gets all <see cref="ComponentSnapshot" /> instances contained in the model configuration.
		/// </summary>
		internal ImmutableArray<ComponentSnapshot> Components { get; private set; }

		/// <summary>
		///     Returns <paramref name="component " /> and all of its subcomponents.
		/// </summary>
		private static IEnumerable<ComponentSnapshot> GetAllComponents(ComponentSnapshot component)
		{
			yield return component;

			foreach (var c in component.SubComponents.SelectMany(GetAllComponents))
				yield return c;
		}
	}
}