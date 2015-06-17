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
	using Modeling;
	using Utilities;

	partial class ModelMetadata
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="ModelMetadata" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly ComponentMetadata.Builder _builder;
			private readonly Model _model;
			private readonly Component _rootComponent;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="model">The model instance the metadata should be built for.</param>
			internal Builder(Model model)
			{
				Requires.NotNull(model, () => model);

				_rootComponent = new RootComponent();
				_builder = new ComponentMetadata.Builder(_rootComponent);
				_model = model;
			}

			/// <summary>
			///     Adds the <paramref name="rootComponent" /> to the model's synthesized root component.
			/// </summary>
			/// <param name="rootComponent">The root component that should be added to the model's synthesized root component.</param>
			public void WithRootComponent(IComponent rootComponent)
			{
				Requires.NotNull(rootComponent, () => rootComponent);
				Requires.OfType<Component>(rootComponent, () => rootComponent);

				_builder.WithSubcomponent(rootComponent);
			}

			/// <summary>
			///     Adds the <paramref name="rootComponents" /> to the model's synthesized root component.
			/// </summary>
			/// <param name="rootComponents">The root components that should be added to the model's synthesized root component.</param>
			public void WithRootComponents(IEnumerable<IComponent> rootComponents)
			{
				Requires.NotNull(rootComponents, () => rootComponents);

				foreach (var subcomponent in rootComponents)
					WithRootComponent(subcomponent);
			}

			/// <summary>
			///     Adds a binding between <paramref name="requiredPort" /> and <paramref name="providedPort" /> to the model's synthesized
			///     root component.
			/// </summary>
			/// <param name="requiredPort">The required port of the port binding.</param>
			/// <param name="providedPort">The provided port of the port binding.</param>
			public void WithBinding(Delegate requiredPort, Delegate providedPort)
			{
				_builder.WithBinding(requiredPort, providedPort);
			}

			/// <summary>
			///     Creates an immutable <see cref="ModelMetadata" /> instance from the current state of the builder.
			/// </summary>
			internal void FinalizeMetadata()
			{
				_builder.FinalizeMetadata();
				_model.Metadata = new ModelMetadata
				{
					Model = _model,
					RootComponent = _rootComponent.Metadata,
					Bindings = _rootComponent.Metadata.Bindings
				};
			}

			/// <summary>
			///     Represents the synthesized root of the component hierarchy created by a model.
			/// </summary>
			private sealed class RootComponent : Component
			{
			}
		}
	}
}