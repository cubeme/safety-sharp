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

	/// <summary>
	///     Provides extension methods for working with S# metadata.
	/// </summary>
	public static class MetadataExtensions
	{
		/// <summary>
		///     Gets the <see cref="ComponentInfo" /> instance for the <paramref name="component" /> instance.
		/// </summary>
		/// <param name="component">The component the <see cref="ComponentInfo" /> instance should be retrieved for.</param>
		public static ComponentInfo GetComponentInfo(this IComponent component)
		{
			return (ComponentInfo)MetadataProvider.GetMetadata(component);
		}

		/// <summary>
		///     Gets the <see cref="FaultInfo" /> instance for the <paramref name="fault" /> instance.
		/// </summary>
		/// <param name="fault">The fault the <see cref="FaultInfo" /> instance should be retrieved for.</param>
		public static FaultInfo GetFaultInfo(this Fault fault)
		{
			return (FaultInfo)MetadataProvider.GetMetadata(fault);
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePatternInfo" /> instance for the <paramref name="occurrencePattern" /> instance.
		/// </summary>
		/// <param name="occurrencePattern">The occurrence pattern the <see cref="OccurrencePatternInfo" /> instance should be retrieved for.</param>
		public static OccurrencePatternInfo GetOccurrenceInfo(this OccurrencePattern occurrencePattern)
		{
			return (OccurrencePatternInfo)MetadataProvider.GetMetadata(occurrencePattern);
		}
	}
}