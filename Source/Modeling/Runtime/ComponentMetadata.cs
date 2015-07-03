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
	using System.Linq;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="Component" /> instance.
	/// </summary>
	public sealed partial class ComponentMetadata : ObjectMetadata
	{
		/// <summary>
		///     Gets the faults affecting the component.
		/// </summary>
		public MemberCollection<FaultMetadata> Faults { get; private set; }

		/// <summary>
		///     Gets the fields declared by the component.
		/// </summary>
		public MemberCollection<FieldMetadata> Fields { get; private set; }

		/// <summary>
		///     Gets the port bindings declared by the component.
		/// </summary>
		public MemberCollection<BindingMetadata> Bindings { get; private set; }

		/// <summary>
		///     Gets the subcomponents contained within the component.
		/// </summary>
		public MemberCollection<ComponentMetadata> Subcomponents { get; private set; }

		/// <summary>
		///     Gets the <see cref="Component" /> instance the metadata is provided for.
		/// </summary>
		public Component Component { get; private set; }

		/// <summary>
		///     Gets the parent <see cref="Component" /> instance within the component hierarchy. Returns <c>null</c> for the
		///     root component.
		/// </summary>
		public ComponentMetadata ParentComponent { get; private set; }

		/// <summary>
		///     Gets the step update methods declared by the component that together make up the <see cref="StepMethod" />.
		/// </summary>
		internal MemberCollection<StepMethodMetadata> UpdateMethods { get; private set; }

		/// <summary>
		///     Gets the step method declared by the component.
		/// </summary>
		public StepMethodMetadata StepMethod { get; private set; }

		/// <summary>
		///     Gets the required ports declared by the component.
		/// </summary>
		public MemberCollection<RequiredPortMetadata> RequiredPorts { get; private set; }

		/// <summary>
		///     Gets the provided ports declared by the component.
		/// </summary>
		public MemberCollection<ProvidedPortMetadata> ProvidedPorts { get; private set; }

		/// <summary>
		///     Gets the root of the component hierarchy.
		/// </summary>
		public ComponentMetadata RootComponent
		{
			get
			{
				if (ParentComponent == null)
					return this;

				return ParentComponent.RootComponent;
			}
		}

		/// <summary>
		///     Gets the user-friendly name of the component.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Visits each component within the component hierarchy in pre-order, invoking <paramref name="visitor" />.
		/// </summary>
		/// <param name="visitor">The visitor that should be invoked on each component within the hierarchy.</param>
		public void VisitPreOrder(Action<ComponentMetadata> visitor)
		{
			Requires.NotNull(visitor, () => visitor);

			Action<ComponentMetadata> preOrder = null;
			preOrder = component =>
			{
				visitor(component);

				foreach (var subcomponent in component.Subcomponents)
					preOrder(subcomponent);
			};

			preOrder(this);
		}

		/// <summary>
		///     Returns a component path leading to this instance, starting at the root. For instance, returns <c>R, A, B</c> for root
		///     component <c>R</c> containing a subcomponent <c>A</c>, which in turn constains this instance with name <c>B</c>.
		/// </summary>
		internal IEnumerable<string> GetPath()
		{
			var components = new List<ComponentMetadata>();
			var root = RootComponent;
			var component = this;

			while (root != component)
			{
				components.Add(component);
				component = component.ParentComponent;
			}

			components.Add(root);
			components.Reverse();
			return components.Select(c => c.Name);
		}
	}
}