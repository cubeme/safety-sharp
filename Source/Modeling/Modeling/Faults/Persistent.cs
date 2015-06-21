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
	using CompilerServices;
	using JetBrains.Annotations;

	/// <summary>
	///     Represents the persistent occurrence pattern where a fault, once active, remains active.
	/// </summary>
	[Metadata("InitializeMetadata")]
	public class Persistent : OccurrencePattern
	{
		/// <summary>
		///     Updates the internal state of the occurrence pattern. Returns <c>true</c> to indicate that the fault is occurring,
		///     <c>false</c> otherwise.
		/// </summary>
		public override bool UpdateOccurrenceState()
		{
			return true;
		}

		/// <summary>
		///     Initializes the metadata of the class.
		/// </summary>
		[UsedImplicitly]
		private void InitializeMetadata()
		{
			MetadataBuilder.WithStepMethod(ReflectionHelpers.GetMethod(typeof(Persistent), "UpdateOccurrenceState", Type.EmptyTypes, typeof(bool)));
		}
	}
}