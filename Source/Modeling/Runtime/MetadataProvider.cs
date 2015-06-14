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
	using Utilities;

	/// <summary>
	///     Provides access to the metadata of various S# types.
	/// </summary>
	internal static class MetadataProvider
	{
		/// <summary>
		///     The object used for thread sychronization.
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
		private static readonly Dictionary<object, object> _metadata =
			new Dictionary<object, object>(ReferenceEqualityComparer<object>.Instance);

		/// <summary>
		///     Maps each supported type with S# metadata to a factory function for its metadata builder.
		/// </summary>
		private static readonly Dictionary<Type, Func<object, object>> _builderCreators = new Dictionary<Type, Func<object, object>>
		{
			{ typeof(Component), component => new ComponentInfo.Builder((Component)component) },
			{ typeof(Fault), fault => new FaultInfo.Builder((Fault)fault) },
			{ typeof(OccurrencePattern), occurrencePattern => new OccurrenceInfo.Builder((OccurrencePattern)occurrencePattern) }
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
		///     Gets the builder instance for <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object instance the builder should be returned for.</param>
		internal static object GetBuilder(object obj)
		{
			Requires.NotNull(obj, () => obj);

			lock (_syncObj)
			{
				Requires.That(!_metadata.ContainsKey(obj), () => obj, "The object's metadata has already been created.");

				object info;
				Requires.That(_builders.TryGetValue(obj, out info), () => obj, "The object's metadata builder has not yet been created.");

				return info;
			}
		}

		/// <summary>
		///     Gets the <see cref="ComponentInfo" /> instance for the <paramref name="component" /> instance.
		/// </summary>
		/// <param name="component">The component the <see cref="ComponentInfo" /> instance should be retrieved for.</param>
		public static ComponentInfo GetComponentInfo(this Component component)
		{
			Requires.NotNull(component, () => component);

			lock (_syncObj)
			{
				object info;
				Requires.That(_metadata.TryGetValue(component, out info), () => component, "The metadata for the component is not yet available.");

				return (ComponentInfo)info;
			}
		}

		/// <summary>
		///     Gets the <see cref="FaultInfo" /> instance for the <paramref name="fault" /> instance.
		/// </summary>
		/// <param name="fault">The fault the <see cref="FaultInfo" /> instance should be retrieved for.</param>
		public static FaultInfo GetFaultInfo(this Fault fault)
		{
			Requires.NotNull(fault, () => fault);

			lock (_syncObj)
			{
				object info;
				Requires.That(_metadata.TryGetValue(fault, out info), () => fault, "The metadata for the fault is not yet available.");

				return (FaultInfo)info;
			}
		}

		/// <summary>
		///     Gets the <see cref="OccurrenceInfo" /> instance for the <paramref name="occurrencePattern" /> instance.
		/// </summary>
		/// <param name="occurrencePattern">The occurrence pattern the <see cref="OccurrenceInfo" /> instance should be retrieved for.</param>
		public static OccurrenceInfo GetOccurrenceInfo(this OccurrencePattern occurrencePattern)
		{
			Requires.NotNull(occurrencePattern, () => occurrencePattern);

			lock (_syncObj)
			{
				object info;
				Requires.That(_metadata.TryGetValue(occurrencePattern, out info), () => occurrencePattern,
					"The metadata for the occurrence pattern is not yet available.");

				return (OccurrenceInfo)info;
			}
		}

		/// <summary>
		///     Adds the finalized <paramref name="metadata" /> for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The object the finalized metadata is added for.</param>
		/// <param name="metadata">The finalized metadata that should be added.</param>
		internal static void FinalizeMetadata(object obj, object metadata)
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