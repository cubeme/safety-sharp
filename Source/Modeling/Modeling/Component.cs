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
	using System.Collections.Immutable;
	using System.Diagnostics;
	using CompilerServices;
	using JetBrains.Annotations;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a S# component.
	/// </summary>
	[Metadata("InitializeMetadata")]
	public abstract partial class Component : IComponent
	{
		[UsedImplicitly]
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Action _updateMethod = null;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="name">The (optional) name of the component.</param>
		protected Component(string name = null)
		{
			MetadataProvider.CreateBuilder(this);

			if (!String.IsNullOrWhiteSpace(name))
				MetadataBuilders.GetBuilder(this).WithName(name);

			MetadataProvider.InitializeMetadata(this);
		}

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="subcomponents">The subcomponents of the component.</param>
		/// <param name="bindings">The port bindings of the component.</param>
		internal Component(ImmutableArray<Component> subcomponents, List<PortBinding> bindings)
			: this()
		{
			Requires.That(!subcomponents.IsDefault, "Expected some subcomponents.");
			Requires.NotNull(bindings, () => bindings);

			_subcomponents = subcomponents;
			_bindings = bindings;
		}

		/// <summary>
		///     Updates the internal state of the component.
		/// </summary>
		[BackingField("_updateMethod")]
		[MethodBehavior("UpdateBehavior")]
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
			MetadataBuilders.GetBuilder(this).WithStepMethod(ReflectionHelpers.GetMethod(typeof(Component), "Update", Type.EmptyTypes, typeof(void)));
		}

		/// <summary>
		///     Empty default behavior of the <see cref="Update" /> method.
		/// </summary>
		[UsedImplicitly]
		private void UpdateBehavior()
		{
		}
	}
}