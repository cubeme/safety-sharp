﻿// The MIT License (MIT)
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
	using System.Diagnostics;
	using Modeling;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="Model" /> instance.
	/// </summary>
	public sealed partial class ModelMetadata : ObjectMetadata
	{
		/// <summary>
		///     The metadata of all components the model consists of.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Lazy<IEnumerable<ComponentMetadata>> _components;

		/// <summary>
		///     Gets the metadata of the synthesized root component of the model.
		/// </summary>
		public ComponentMetadata RootComponent { get; private set; }

		/// <summary>
		///     Gets the <see cref="Model" /> instance the metadata is provided for.
		/// </summary>
		public Model Model { get; private set; }

		/// <summary>
		///     Gets the metadata of all components the model consists of.
		/// </summary>
		public IEnumerable<ComponentMetadata> Components
		{
			get { return _components.Value; }
		}

		/// <summary>
		///     Gets the port bindings declared by the model.
		/// </summary>
		public MemberCollection<BindingMetadata> Bindings { get; private set; }
	}
}