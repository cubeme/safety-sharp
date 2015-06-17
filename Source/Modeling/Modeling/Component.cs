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
	using System.Diagnostics;
	using CompilerServices;
	using JetBrains.Annotations;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a S# component.
	/// </summary>
	[Metadata("InitializeMetadata")]
	public abstract class Component : MetadataObject<ComponentMetadata, ComponentMetadata.Builder>, IComponent
	{
		/// <summary>
		///     The user-provided name of the component.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private readonly string _name;

		[UsedImplicitly]
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Action _updateMethod = null;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		protected Component()
			: this(null)
		{
		}

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="name">The (optional) name of the component.</param>
		protected Component(string name)
			: base(obj => new ComponentMetadata.Builder((Component)obj))
		{
			_name = name;
		}

		/// <summary>
		///     Gets all required ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic RequiredPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
		}

		/// <summary>
		///     Gets all provided ports declared by the component that are accessible from the location of the caller.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		public dynamic ProvidedPorts
		{
			get { throw new InvalidOperationException("This property cannot be used outside of a port binding expression."); }
		}

		/// <summary>
		///     Updates the internal state of the component.
		/// </summary>
		[BackingField("_updateMethod")]
		[IntendedBehavior("UpdateBehavior")]
		public virtual void Update()
		{
			_updateMethod();
		}

		/// <summary>
		///     Initializes the metadata of the class.
		/// </summary>
		[UsedImplicitly]
		private void InitializeMetadata()
		{
			if (!String.IsNullOrWhiteSpace(_name))
				MetadataBuilder.WithName(_name);
			MetadataBuilder.WithStepMethod(ReflectionHelpers.GetMethod(typeof(Component), "Update", Type.EmptyTypes, typeof(void)));
		}

		/// <summary>
		///     Empty default behavior of the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private void UpdateBehavior()
		{
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the current component's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		protected static void SetInitialValues<T>(T field, params T[] values)
		{
			Requires.CompilationTransformation();
		}

		/// <summary>
		///     Adds the <paramref name="portBinding" /> to the current component's bindings.
		/// </summary>
		/// <param name="portBinding">
		///     The port binding expression of the form
		///     <c>component1.RequiredPorts.Port1 = component2.ProvidedPorts.Port2</c> that declares the binding.
		/// </param>
		protected static void Bind(object portBinding)
		{
			Requires.CompilationTransformation();
		}
	}
}