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
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a model of a safety-critical system.
	/// </summary>
	public class Model : MetadataObject<ModelMetadata, ModelMetadata.Builder>
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public Model()
			: base(obj => new ModelMetadata.Builder((Model)obj))
		{
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
		public void AddRootComponents(params IComponent[] rootComponents)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Explicitly seals the model, preventing any future metadata modifications such as adding new root components or bindings.
		///     This method is called implicitly when the model is analyzed or simulated. If the model has already been sealed, this
		///     method is a no-op.
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
		public void Bind(object portBinding)
		{
			Requires.CompilationTransformation();
		}
	}
}