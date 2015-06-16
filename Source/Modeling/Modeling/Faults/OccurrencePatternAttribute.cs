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

namespace SafetySharp.Modeling.Faults
{
	using System;
	using Utilities;

	/// <summary>
	///     When applied to a <see cref="Fault" /> declaration, determines the <see cref="OccurrencePattern" /> of the fault.
	/// </summary>
	[AttributeUsage(AttributeTargets.Class, AllowMultiple = false, Inherited = false)]
	public class OccurrencePatternAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="type">The <see cref="OccurrencePattern" /> of the marked fault.</param>
		public OccurrencePatternAttribute(Type type)
		{
			Type = type;
		}

		/// <summary>
		///     Gets the <see cref="OccurrencePattern" /> type.
		/// </summary>
		public Type Type { get; private set; }

		/// <summary>
		///     Creates a new instance of the <see cref="OccurrencePattern" />.
		/// </summary>
		internal OccurrencePattern CreateInstance()
		{
			Requires.That(typeof(OccurrencePattern).IsAssignableFrom(Type),
				"An occurrence pattern must be derived from '{0}'.", typeof(OccurrencePattern).FullName);
			Requires.That(Type.GetConstructor(Type.EmptyTypes) != null,
				"Occurrence pattern '{0}' must declare a default constructor.", Type.FullName);

			return (OccurrencePattern)Activator.CreateInstance(Type);
		}
	}
}