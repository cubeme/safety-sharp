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
	using Modeling.Faults;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="OccurrencePattern" /> instance.
	/// </summary>
	public sealed partial class OccurrencePatternMetadata : ObjectMetadata
	{
		/// <summary>
		///     The fault that is affected by the occurrence pattern.
		/// </summary>
		private Fault _fault;

		/// <summary>
		///     Gets the fields declared by the occurrence pattern.
		/// </summary>
		public MemberCollection<FieldMetadata> Fields { get; private set; }

		/// <summary>
		///     Gets the step update methods declared by the occurrence pattern that together make up the <see cref="StepMethod" />.
		/// </summary>
		internal MemberCollection<StepMethodMetadata> UpdateMethods { get; private set; }

		/// <summary>
		///     Gets the step method declared by the component.
		/// </summary>
		public StepMethodMetadata StepMethod { get; private set; }

		/// <summary>
		///     Gets the metadata of the declaring fault that is affected by the occurrence pattern.
		/// </summary>
		public FaultMetadata DeclaringFault
		{
			get { return _fault.GetMetadata(); }
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePattern" /> instance the metadata is provided for.
		/// </summary>
		public OccurrencePattern OccurrencePattern { get; private set; }
	}
}