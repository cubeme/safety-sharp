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
	using System.Reflection;
	using CompilerServices;
	using Modeling;
	using Modeling.Faults;
	using Utilities;

	/// <summary>
	///     Provides access to the metadata of various S# types.
	/// </summary>
	internal static class MetadataProvider
	{
		/// <summary>
		///     The object used for thread synchronization.
		/// </summary>
		private static readonly object _syncObj = new object();

		/// <summary>
		///     The currently available metadata builders.
		/// </summary>
		private static readonly Dictionary<object, object> _builders =
			new Dictionary<object, object>(ReferenceEqualityComparer<object>.Instance);

		/// <summary>
		///     The currently available metadata instances.
		/// </summary>
		private static readonly Dictionary<object, ObjectMetadata> _metadata =
			new Dictionary<object, ObjectMetadata>(ReferenceEqualityComparer<object>.Instance);

		/// <summary>
		///     Maps each supported type with S# metadata to a factory function for its metadata builder.
		/// </summary>
		private static readonly Dictionary<Type, Func<object, object>> _builderCreators = new Dictionary<Type, Func<object, object>>
		{
			{ typeof(Component), component => new ComponentMetadata.Builder((Component)component) },
			{ typeof(Fault), fault => new FaultMetadata.Builder((Fault)fault) },
			{ typeof(OccurrencePattern), occurrencePattern => new OccurrencePatternMetadata.Builder((OccurrencePattern)occurrencePattern) }
		};

		/// <summary>
		///     Creates the metadata builder for <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the metadata builder should be created for.</param>
		internal static void CreateBuilder<T>(T obj)
			where T : class
		{
			Requires.NotNull(obj, () => obj);
			Requires.That(_builderCreators.ContainsKey(typeof(T)), () => obj,
				"Type '{0}' does not expose any S#-specific metadata.", typeof(T).FullName);

			lock (_syncObj)
			{
				Requires.That(!_builders.ContainsKey(obj), () => obj, "A builder has already been created.");
				Requires.That(!_metadata.ContainsKey(obj), () => obj, "The object's metadata has already been created.");

				_builders.Add(obj, _builderCreators[typeof(T)](obj));
			}
		}

		/// <summary>
		///     Tries to get the builder instance for <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object instance the builder should be returned for.</param>
		/// <param name="builder">Returns the builder if it exists.</param>
		internal static bool TryGetBuilder(object obj, out object builder)
		{
			Requires.NotNull(obj, () => obj);

			lock (_syncObj)
			{
				return _builders.TryGetValue(obj, out builder);
			}
		}

		/// <summary>
		///     Gets the builder instance for <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object instance the builder should be returned for.</param>
		internal static object GetBuilder(object obj)
		{
			Requires.NotNull(obj, () => obj);

			object builder;
			Requires.That(TryGetBuilder(obj, out builder), () => obj, "The object's metadata builder has not yet been created.");

			return builder;
		}

		/// <summary>
		///     Gets the metadata for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the metadata should be returned for.</param>
		internal static ObjectMetadata GetMetadata(object obj)
		{
			Requires.NotNull(obj, () => obj);

			lock (_syncObj)
			{
				ObjectMetadata metadata;
				Requires.That(_metadata.TryGetValue(obj, out metadata), () => obj, "The object's metadata has not yet been created.");

				return metadata;
			}
		}

		/// <summary>
		///     Adds the finalized <paramref name="metadata" /> for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the finalized metadata is added for.</param>
		/// <param name="metadata">The finalized metadata that should be added.</param>
		internal static void FinalizeMetadata(object obj, ObjectMetadata metadata)
		{
			Requires.NotNull(obj, () => obj);
			Requires.NotNull(metadata, () => metadata);

			lock (_syncObj)
			{
				_metadata.Add(obj, metadata);
				_builders.Remove(obj);
			}
		}

		/// <summary>
		///     Initializes <paramref name="obj" />'s S# metadata.
		/// </summary>
		/// <param name="obj">The object whose metadata should be initialized.</param>
		internal static void InitializeMetadata(object obj)
		{
			Requires.NotNull(obj, () => obj);

			lock (_syncObj)
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
						metadataInitialization.InitializeMetadata(type, obj);
				};

				initialize(obj.GetType());
			}
		}
	}
}