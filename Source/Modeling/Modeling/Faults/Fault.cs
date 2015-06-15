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
	using System.Reflection;
	using CompilerServices;
	using JetBrains.Annotations;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Represents a base class for all faults.
	/// </summary>
	[Metadata("InitializeMetadata")]
	public abstract class Fault
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		protected Fault()
		{
			MetadataProvider.CreateBuilder(this);

			var occurrencePattern = GetType().GetCustomAttribute<OccurrencePatternAttribute>();
			Requires.That(occurrencePattern != null, "Expected fault to be marked with an instance of '{0}'.",
				typeof(OccurrencePatternAttribute).FullName);

			MetadataBuilders.GetBuilder(this).WithOccurrencePattern((OccurrencePattern)Activator.CreateInstance(occurrencePattern.Type));
			MetadataProvider.InitializeMetadata(this);
		}

		/// <summary>
		///     Updates the internal state of the fault.
		/// </summary>
		public virtual void Update()
		{
		}

		/// <summary>
		///     Initializes the metadata of the class.
		/// </summary>
		[UsedImplicitly]
		private void InitializeMetadata()
		{
			MetadataBuilders.GetBuilder(this).WithStepMethod(ReflectionHelpers.GetMethod(typeof(Fault), "Update", Type.EmptyTypes, typeof(void)));
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the current fault's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		protected static void SetInitialValues<T>(T field, params T[] values)
		{
			Requires.CompilationTransformation();
		}
	}
}