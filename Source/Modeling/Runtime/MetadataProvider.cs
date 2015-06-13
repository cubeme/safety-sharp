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
		///     The currently available <see cref="ComponentInfo.Builder" /> instances.
		/// </summary>
		internal static readonly Dictionary<Component, ComponentInfo.Builder> ComponentBuilders =
			new Dictionary<Component, ComponentInfo.Builder>(ReferenceEqualityComparer<Component>.Instance);

		/// <summary>
		///     The currently available <see cref="FaultInfo.Builder" /> instances.
		/// </summary>
		internal static readonly Dictionary<Fault, FaultInfo.Builder> FaultBuilders =
			new Dictionary<Fault, FaultInfo.Builder>(ReferenceEqualityComparer<Fault>.Instance);

		/// <summary>
		///     The currently available <see cref="OccurrenceInfo.Builder" /> instances.
		/// </summary>
		internal static readonly Dictionary<OccurrencePattern, OccurrenceInfo.Builder> OccurrencePatternBuilders =
			new Dictionary<OccurrencePattern, OccurrenceInfo.Builder>(ReferenceEqualityComparer<OccurrencePattern>.Instance);

		/// <summary>
		///     Gets the currently available <see cref="ComponentInfo" /> instances.
		/// </summary>
		internal static readonly Dictionary<Component, ComponentInfo> Components =
			new Dictionary<Component, ComponentInfo>(ReferenceEqualityComparer<Component>.Instance);

		/// <summary>
		///     Gets the currently available <see cref="FaultInfo" /> instances.
		/// </summary>
		internal static readonly Dictionary<Fault, FaultInfo> Faults =
			new Dictionary<Fault, FaultInfo>(ReferenceEqualityComparer<Fault>.Instance);

		/// <summary>
		///     Gets the currently available <see cref="OccurrenceInfo" /> instances.
		/// </summary>
		internal static readonly Dictionary<OccurrencePattern, OccurrenceInfo> OccurrencePatterns =
			new Dictionary<OccurrencePattern, OccurrenceInfo>(ReferenceEqualityComparer<OccurrencePattern>.Instance);

		/// <summary>
		///     Gets the <see cref="ComponentInfo" /> instance for the <paramref name="component" /> instance.
		/// </summary>
		/// <param name="component">The component the <see cref="ComponentInfo" /> instance should be retrieved for.</param>
		public static ComponentInfo GetComponentInfo(this Component component)
		{
			Requires.NotNull(component, () => component);

			ComponentInfo info;
			Requires.That(Components.TryGetValue(component, out info), () => component, "The metadata for the component is not yet available.");

			return info;
		}

		/// <summary>
		///     Gets the <see cref="FaultInfo" /> instance for the <paramref name="fault" /> instance.
		/// </summary>
		/// <param name="fault">The fault the <see cref="FaultInfo" /> instance should be retrieved for.</param>
		public static FaultInfo GetFaultInfo(this Fault fault)
		{
			Requires.NotNull(fault, () => fault);

			FaultInfo info;
			Requires.That(Faults.TryGetValue(fault, out info), () => fault, "The metadata for the fault is not yet available.");

			return info;
		}

		/// <summary>
		///     Gets the <see cref="OccurrenceInfo" /> instance for the <paramref name="occurrencePattern" /> instance.
		/// </summary>
		/// <param name="occurrencePattern">The occurrence pattern the <see cref="OccurrenceInfo" /> instance should be retrieved for.</param>
		public static OccurrenceInfo GetOccurrenceInfo(this OccurrencePattern occurrencePattern)
		{
			Requires.NotNull(occurrencePattern, () => occurrencePattern);

			OccurrenceInfo info;
			Requires.That(OccurrencePatterns.TryGetValue(occurrencePattern, out info), () => occurrencePattern,
				"The metadata for the occurrence pattern is not yet available.");

			return info;
		}

		/// <summary>
		///     Initializes <paramref name="obj" />'s S# metadata.
		/// </summary>
		/// <param name="obj">The object whose metadata should be initialized.</param>
		internal static void InitializeMetadata(object obj)
		{
			Requires.NotNull(obj, () => obj);

			// The metadata of base types must be initialized first
			Action<Type> initialize = null;
			initialize = type =>
			{
				if (type == typeof(object))
					return;

				initialize(type.BaseType);

				var metadataInitialization = type.GetCustomAttribute<MetadataInitializationAttribute>();
				if (metadataInitialization != null)
					metadataInitialization.InitializeMetadata(type, obj);
			};

			initialize(obj.GetType());
		}
	}
}