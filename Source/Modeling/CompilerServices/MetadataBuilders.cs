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

namespace SafetySharp.CompilerServices
{
	using System;
	using Modeling;
	using Modeling.Faults;
	using Runtime;

	/// <summary>
	///     Provides access to and manages the lifetime of the various metadata builder kinds.
	/// </summary>
	public static class MetadataBuilders
	{
		/// <summary>
		///     Gets the <see cref="ComponentMetadata.Builder" /> instance for <paramref name="component" />. Throws a
		///     <see cref="InvalidOperationException" /> when <paramref name="component" />'s metadata has already
		///     been fully initialized.
		/// </summary>
		/// <param name="component">The component instance the builder should be returned for.</param>
		public static ComponentMetadata.Builder GetBuilder(Component component)
		{
			return (ComponentMetadata.Builder)MetadataProvider.GetBuilder(component);
		}

		/// <summary>
		///     Gets the <see cref="FaultMetadata.Builder" /> instance for <paramref name="fault" />. Throws a
		///     <see cref="InvalidOperationException" /> when <paramref name="fault" />'s metadata has already
		///     been fully initialized.
		/// </summary>
		/// <param name="fault">The fault instance the builder should be returned for.</param>
		public static FaultMetadata.Builder GetBuilder(Fault fault)
		{
			return (FaultMetadata.Builder)MetadataProvider.GetBuilder(fault);
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePatternMetadata.Builder" /> instance for <paramref name="occurrencePattern" />. Throws a
		///     <see cref="InvalidOperationException" /> when <paramref name="occurrencePattern" />'s metadata has already
		///     been fully initialized.
		/// </summary>
		/// <param name="occurrencePattern">The occurrence pattern instance the builder should be returned for.</param>
		public static OccurrencePatternMetadata.Builder GetBuilder(OccurrencePattern occurrencePattern)
		{
			return (OccurrencePatternMetadata.Builder)MetadataProvider.GetBuilder(occurrencePattern);
		}
	}
}