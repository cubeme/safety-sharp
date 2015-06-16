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

namespace SafetySharp.Modeling.Faults
{
	using System;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a base class for all fault occurrence patterns.
	/// </summary>
	public abstract class OccurrencePattern
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		protected OccurrencePattern()
		{
			MetadataProvider.CreateBuilder(this);
			MetadataProvider.InitializeMetadata(this);
		}

		/// <summary>
		///     Updates the internal state of the occurrence pattern. Returns <c>true</c> to indicate that the fault is occurring,
		///     <c>false</c> otherwise.
		/// </summary>
		public abstract bool UpdateOccurrenceState();

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the current occurrence pattern's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		protected static void SetInitialValues<T>(T field, params T[] values)
		{
			Requires.CompilationTransformation();
		}
	}
}