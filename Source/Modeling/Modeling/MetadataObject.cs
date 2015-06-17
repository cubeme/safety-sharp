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
	using System.Reflection;
	using CompilerServices;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a base class for all S# objects that provide S# metadata.
	/// </summary>
	/// <typeparam name="TMetadata">The type of the object's metadata.</typeparam>
	/// <typeparam name="TMetadataBuilder">The type of the object's metadata builder.</typeparam>
	public abstract class MetadataObject<TMetadata, TMetadataBuilder> : IMetadataObject
		where TMetadata : ObjectMetadata
		where TMetadataBuilder : class
	{
		/// <summary>
		///     The object's metadata.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private TMetadata _metadata;

		/// <summary>
		///     The object's metadata builder.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private TMetadataBuilder _metadataBuilder;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="createBuilder">The function that should be used to initialize the object's metadata builder.</param>
		protected MetadataObject(Func<object, TMetadataBuilder> createBuilder)
		{
			Requires.NotNull(createBuilder, () => createBuilder);

			_metadataBuilder = createBuilder(this);
			InitializeMetadata();
		}

		/// <summary>
		///     Gets or sets the object's metadata. Once the metadata has been set, all future metadata modifications are disallowed.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		internal TMetadata Metadata
		{
			get
			{
				Requires.That(_metadata != null, "The object's metadata has not yet been created.");
				return _metadata;
			}
			set
			{
				Requires.That(_metadata == null, "The object's metadata has already been set.");
				_metadata = value;
				_metadataBuilder = null;
			}
		}

		/// <summary>
		///     Gets the object's metadata builder.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		internal TMetadataBuilder MetadataBuilder
		{
			get
			{
				Requires.That(_metadataBuilder != null, "The object's metadata has already been initialized.");
				return _metadataBuilder;
			}
		}

		/// <summary>
		///     Gets a value indicating whether the object's metadata has been finalized.
		/// </summary>
		internal bool IsMetadataFinalized
		{
			get { return _metadata != null; }
		}

		/// <summary>
		///     Gets a value indicating whether the object's metadata has been finalized.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		bool IMetadataObject.IsMetadataFinalized
		{
			get { return IsMetadataFinalized; }
		}

		/// <summary>
		///     Gets the object's metadata.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		ObjectMetadata IMetadataObject.Metadata
		{
			get { return Metadata; }
		}

		/// <summary>
		///     Initializes the object's metadata by invoking the method indicated by the <see cref="MetadataAttribute" /> at each level
		///     of the object's inheritance hierarchy.
		/// </summary>
		private void InitializeMetadata()
		{
			// The metadata of base types must be initialized first
			Action<Type> initialize = null;
			initialize = type =>
			{
				if (type == typeof(object))
					return;

				initialize(type.BaseType);

				var metadataInitialization = type.GetCustomAttribute<MetadataAttribute>();
				if (metadataInitialization != null)
					metadataInitialization.InitializeMetadata(type, this);
			};

			initialize(GetType());
		}
	}
}