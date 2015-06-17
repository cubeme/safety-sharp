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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a model of a safety-critical system.
	/// </summary>
	public partial class Model : MetadataObject<ModelMetadata, ModelMetadata.Builder>
	{
		/// <summary>
		///     The list of port bindings established by the model.
		/// </summary>
		private readonly List<PortBinding> _bindings = new List<PortBinding>();

		/// <summary>
		///     All of the components contained in the model.
		/// </summary>
		private List<Component> _components;

		/// <summary>
		///     The root components of the model.
		/// </summary>
		private List<Component> _roots;

		/// <summary>
		///     The synthesized root component of the model that is the parent of all <see cref="_roots" />.
		/// </summary>
		private RootComponent _synthesizedRoot;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public Model()
			: base(obj => new ModelMetadata.Builder((Model)obj))
		{
		}

		/// <summary>
		///     Gets the root <see cref="Component" />s of the model.
		/// </summary>
		internal List<Component> Roots
		{
			get
			{
				RequiresIsSealed();
				return _roots;
			}
		}

		/// <summary>
		///     Gets the synthesized root component of the model.
		/// </summary>
		internal RootComponent SynthesizedRoot
		{
			get
			{
				RequiresIsSealed();
				return _synthesizedRoot;
			}
		}

		/// <summary>
		///     Gets all <see cref="Component" />s contained in the model.
		/// </summary>
		internal List<Component> Components
		{
			get
			{
				RequiresIsSealed();
				return _components;
			}
		}

		/// <summary>
		///     Adds the <see cref="rootComponent" /> to the model.
		/// </summary>
		/// <param name="rootComponent">The root component that should be added.</param>
		public void AddRootComponent(IComponent rootComponent)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Adds the <see cref="rootComponents" /> to the model.
		/// </summary>
		/// <param name="rootComponents">The root components that should be added.</param>
		public void AddRootComponent(params IComponent[] rootComponents)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Explicitely seals the model, preventing any future metadata changes such as adding new root components or bindings. This
		///     method is called implicitly when the model is analyzed or simulated. If the model has already been sealed, this method
		///     is a no-op.
		/// </summary>
		public void Seal()
		{
			if (!IsMetadataFinalized)
				MetadataBuilder.FinalizeMetadata();
		}

		/// <summary>
		///     Adds the <paramref name="portBinding" /> to the model's bindings.
		/// </summary>
		/// <param name="portBinding">
		///     The port binding expression of the form
		///     <c>component1.RequiredPorts.Port1 = component2.ProvidedPorts.Port2</c> that declares the binding.
		/// </param>
		public void Bind(PortBinding portBinding)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Recursively gets all components contained in the model.
		/// </summary>
		/// <param name="knownComponents">The set of components that has already been found.</param>
		/// <param name="component">The component whose subcomponents are being retrieved.</param>
		private IEnumerable<Component> GetAllComponents(HashSet<Component> knownComponents, Component component)
		{
			yield return component;

			if (!knownComponents.Add(component))
				yield break;

			foreach (var subcomponent in component.Subcomponents)
			{
				foreach (var c in GetAllComponents(knownComponents, subcomponent))
					yield return c;
			}
		}

		/// <summary>
		///     Sets the root components of the model.
		/// </summary>
		/// <param name="rootComponents">The root components of the model.</param>
		public void SetRootComponents(params Component[] rootComponents)
		{
			Requires.NotNull(rootComponents, () => rootComponents);
			Requires.That(rootComponents.Length > 0, () => rootComponents, "There must be at least one root component.");
			Requires.That(_components == null, "The root components have already been set.");
			Requires.That(!_isSealed, "The model's metadata has already been finalized.");

			// Disallow future modifications of the components' metadata
			for (var i = 0; i < rootComponents.Length; ++i)
			{
				// Make sure that we won't finalize the same component twice (might happen when components are shared, will be detected later)
				if (rootComponents[i].IsMetadataFinalized)
					continue;

				// Add the index to the name to disambiguate roots in exception messages
				rootComponents[i].FinalizeMetadata(null, String.Format("{0}.{1}{2}", Component.SynthesizedRootName,
					rootComponents[i].GetType().Name, i), i);
			}

			// Store the root components and collect all components of the model
			var knownComponents = new HashSet<Component>();
			_roots = rootComponents.ToList();
			_components = _roots.SelectMany(root => GetAllComponents(knownComponents, root)).ToList();

			// Ensure that there are no shared components
			var sharedComponents = _components
				.GroupBy(component => component)
				.Where(group => group.Count() > 1)
				.Select(group => group.Key)
				.ToArray();

			if (sharedComponents.Length > 0)
				throw new SharedComponentsException(sharedComponents);
		}

		/// <summary>
		///     Finds the component with the <paramref name="mangledName" /> within the model.
		/// </summary>
		/// <param name="mangledName">The name of the component that should be returned.</param>
		internal Component FindComponent(string mangledName)
		{
			RequiresIsSealed();
			Requires.NotNullOrWhitespace(mangledName, () => mangledName);

			if (mangledName == _synthesizedRoot.Name)
				return _synthesizedRoot;

			return _components.Single(component => component.Name == mangledName);
		}

		/// <summary>
		///     Returns the type of the component with the <paramref name="mangledName" /> within the model.
		/// </summary>
		/// <param name="mangledName">The name of the component that should be returned.</param>
		internal Type GetTypeOfComponent(string mangledName)
		{
			RequiresIsSealed();
			return FindComponent(mangledName).GetType();
		}
	}
}