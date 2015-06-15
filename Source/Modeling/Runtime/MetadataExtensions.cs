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
	using Modeling;
	using Modeling.Faults;

	/// <summary>
	///     Provides extension methods for working with S# metadata.
	/// </summary>
	public static class MetadataExtensions
	{
		/// <summary>
		///     Gets the <see cref="ObjectMetadata" /> instance for the <paramref name="obj" />.
		/// </summary>
		/// <param name="obj">The component the <see cref="ObjectMetadata" /> instance should be retrieved for.</param>
		public static ObjectMetadata GetMetadata(this object obj)
		{
			return MetadataProvider.GetMetadata(obj);
		}

		/// <summary>
		///     Gets the <see cref="ComponentMetadata" /> instance for the <paramref name="component" /> instance.
		/// </summary>
		/// <param name="component">The component the <see cref="ComponentMetadata" /> instance should be retrieved for.</param>
		public static ComponentMetadata GetMetadata(this IComponent component)
		{
			return (ComponentMetadata)MetadataProvider.GetMetadata(component);
		}

		/// <summary>
		///     Gets the <see cref="FaultMetadata" /> instance for the <paramref name="fault" /> instance.
		/// </summary>
		/// <param name="fault">The fault the <see cref="FaultMetadata" /> instance should be retrieved for.</param>
		public static FaultMetadata GetMetadata(this Fault fault)
		{
			return (FaultMetadata)MetadataProvider.GetMetadata(fault);
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePatternMetadata" /> instance for the <paramref name="occurrencePattern" /> instance.
		/// </summary>
		/// <param name="occurrencePattern">
		///     The occurrence pattern the <see cref="OccurrencePatternMetadata" /> instance should be retrieved
		///     for.
		/// </param>
		public static OccurrencePatternMetadata GetMetadata(this OccurrencePattern occurrencePattern)
		{
			return (OccurrencePatternMetadata)MetadataProvider.GetMetadata(occurrencePattern);
		}
	}
}