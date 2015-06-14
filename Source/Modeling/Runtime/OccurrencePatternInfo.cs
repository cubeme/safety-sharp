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
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="OccurrencePattern" /> instance.
	/// </summary>
	public sealed partial class OccurrencePatternInfo
	{
		/// <summary>
		///     The fault that is affected by the occurrence pattern.
		/// </summary>
		private readonly Fault _fault;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="occurrencePattern"></param>
		/// <param name="fault"></param>
		internal OccurrencePatternInfo(OccurrencePattern occurrencePattern, Fault fault)
		{
			Requires.NotNull(occurrencePattern, () => occurrencePattern);
			Requires.NotNull(fault, () => fault);

			_fault = fault;
			OccurrencePattern = occurrencePattern;
		}

		/// <summary>
		///     Gets the metadata of the fault that is affected by the occurrence pattern.
		/// </summary>
		public FaultInfo Fault
		{
			get { return _fault.GetFaultInfo(); }
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePattern" /> instance the metadata is provided for.
		/// </summary>
		public OccurrencePattern OccurrencePattern { get; private set; }
	}
}