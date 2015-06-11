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

	partial class OccurrenceInfo
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="OccurrenceInfo" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly OccurrencePattern _occurrencePattern = null;

			internal Builder(OccurrencePattern c)
			{
			}

			public void WithUpdateMethod(MethodInfo method, Func<Expression> createBody = null)
			{
			}

			public void WithField(FieldInfo field)
			{
			}

			/// <summary>
			///     Creates an immutable <see cref="OccurrenceInfo" /> instance from the current state of the builder and makes it available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			/// <param name="fault">The fault that is affected by the occurrence pattern.</param>
			internal OccurrenceInfo RegisterMetadata(Fault fault)
			{
				Requires.NotNull(fault, () => fault);

				var info = new OccurrenceInfo(fault);
				MetadataProvider.OccurrencePatterns.Add(_occurrencePattern, info);
				MetadataProvider.OccurrencePatternBuilders.Remove(_occurrencePattern);

				return info;
			}
		}
	}
}