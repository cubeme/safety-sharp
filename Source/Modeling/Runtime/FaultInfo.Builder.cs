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
	using System.Linq.Expressions;
	using System.Reflection;
	using Modeling;
	using Utilities;

	partial class FaultInfo
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="FaultInfo" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly Fault _fault;
			private OccurrenceInfo _occurrencePattern;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="fault">The fault instance the metadata should be built for.</param>
			internal Builder(Fault fault)
			{
				Requires.NotNull(fault, () => fault);
				_fault = fault;
			}

			/// <summary>
			///     Adds the <paramref name="faultEffect" /> to the fault's metadata. The <paramref name="createBody" /> must not be
			///     <c>null</c> if the component is intended to be used with S# analysis techniques.
			/// </summary>
			/// <param name="faultEffect">The fault effect that should be added.</param>
			/// <param name="affectedMethod">The affected method of the affected component.</param>
			/// <param name="createBody">The callback that should be used to retrieve the body of the fault effect.</param>
			public void WithEffect(MethodInfo faultEffect, MethodInfo affectedMethod, Func<Expression> createBody = null)
			{
				Requires.NotNull(faultEffect, () => faultEffect);
				Requires.NotNull(affectedMethod, () => affectedMethod);
			}

			/// <summary>
			///     Sets the <paramref name="occurrencePattern" /> that affects the fault.
			/// </summary>
			/// <param name="occurrencePattern">The occurrence pattern that should be set.</param>
			public void WithOccurrencePattern(OccurrenceInfo occurrencePattern)
			{
				Requires.NotNull(occurrencePattern, () => occurrencePattern);
				Requires.That(occurrencePattern.Fault == _fault, () => occurrencePattern, "The occurrence pattern affects another fault.");

				_occurrencePattern = occurrencePattern;
			}

			/// <summary>
			///     Creates an immutable <see cref="FaultInfo" /> instance from the current state of the builder and makes it available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			/// <param name="component">The component that is affected by the fault.</param>
			internal FaultInfo FinalizeMetadata(Component component)
			{
				Requires.NotNull(component, () => component);

				var info = new FaultInfo(component, _fault);
				MetadataProvider.Faults.Add(_fault, info);
				MetadataProvider.FaultBuilders.Remove(_fault);

				return info;
			}
		}
	}
}