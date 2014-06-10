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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using Utilities;

	/// <summary>
	/// 
	/// </summary>
	public abstract class ModelConfiguration : IIsImmutable
	{
		/// <summary>
		///     All of the components contained in the model configuration.
		/// </summary>
		private ImmutableArray<Component> _components = ImmutableArray<Component>.Empty;

		/// <summary>
		///     The partition root components of the configuration.
		/// </summary>
		private ImmutableArray<Component> _partitionRoots = ImmutableArray<Component>.Empty;

		/// <summary>
		///     Gets the partition root <see cref="Component" />s of the configuration.
		/// </summary>
		internal ImmutableArray<Component> PartitionRoots
		{
			get
			{
				Requires.IsImmutable(this);
				return _partitionRoots;
			}
		}

		/// <summary>
		///     Gets all <see cref="Component" />s contained in the model configuration.
		/// </summary>
		internal ImmutableArray<Component> Components
		{
			get
			{
				Requires.IsImmutable(this);
				return _components;
			}
		}

		/// <summary>
		///     Gets a value indicating whether the model configuration is sealed and can no longer be modified.
		/// </summary>
		public bool IsImmutable { get; private set; }

		/// <summary>
		///     Sets the <paramref name="components" /> as the root components of the partitions of the model configuration.
		/// </summary>
		/// <param name="components">The components that should be set as root components of partitions.</param>
		protected void SetPartitions(params Component[] components)
		{
			Requires.NotNull(components, () => components);
			Requires.ArgumentSatisfies(components.Length > 0, () => components, "No partition roots have been set for the model configuration.");
			Requires.NotImmutable(this);
			Requires.That(_components.IsEmpty, "This method can only be called once on any given model configuration.");

			// Disallow future modifications of the components
			for (var i = 0; i < components.Length; ++i)
				components[i].ToImmutable("Root" + i);

			// Store the partition roots and collect all components of the model configuration
			_partitionRoots = components.ToImmutableArray();
			_components = _partitionRoots.SelectMany(GetAllComponents).ToImmutableArray();

			// Ensure that there are no shared components
			var hashSet = new HashSet<Component>();
			var sharedComponent = _components.FirstOrDefault(component => !hashSet.Add(component));

			if (sharedComponent == null)
				return;

			const string message = "A component instance of type '{0}' has been found in multiple locations of the component tree.";
			throw new InvalidOperationException(String.Format(message, sharedComponent.GetType().FullName));
		}

		/// <summary>
		///     Marks the model configuration as immutable, disallowing any future state modifications.
		/// </summary>
		internal void ToImmutable()
		{
			Requires.That(_components.Length > 0, "No partition roots have been set for the model configuration.");
			Requires.NotImmutable(this);

			IsImmutable = true;
		}

		/// <summary>
		///     Returns <paramref name="component " /> and all of its subcomponents.
		/// </summary>
		private static IEnumerable<Component> GetAllComponents(Component component)
		{
			yield return component;

			foreach (var c in component.SubComponents.SelectMany(GetAllComponents))
				yield return c;
		}
	}
}