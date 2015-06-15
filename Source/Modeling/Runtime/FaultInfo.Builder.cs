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
	using System.Collections.Generic;
	using System.Linq;
	using System.Reflection;
	using CompilerServices;
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
			private readonly Dictionary<FieldInfo, object[]> _fields = new Dictionary<FieldInfo, object[]>();
			private OccurrencePatternInfo _occurrencePattern;

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
			///     Sets the initial <paramref name="values" /> of the component's <paramref name="field" />.
			/// </summary>
			/// <param name="field">The field whose initial values should be set.</param>
			/// <param name="values">The initial values of the field.</param>
			public void WithInitialValues(FieldInfo field, params object[] values)
			{
				Requires.NotNull(field, () => field);
				Requires.NotNull(values, () => values);
				Requires.That(values.Length > 0, () => values, "At least one value must be provided.");
				Requires.That(_fields.ContainsKey(field), () => field, "The given field is unknown.");

				var typesMatch = values.All(value => value.GetType() == field.FieldType);
				Requires.That(typesMatch, () => values, "Expected all values to be of type '{0}'.", field.FieldType);

				_fields[field] = values;
			}

			/// <summary>
			///     Adds the <paramref name="faultEffect" /> to the fault's metadata.
			/// </summary>
			/// <param name="faultEffect">The fault effect that should be added.</param>
			/// <param name="affectedMethod">The affected method of the affected component.</param>
			public void WithEffect(MethodInfo faultEffect, MethodInfo affectedMethod)
			{
				Requires.NotNull(faultEffect, () => faultEffect);
				Requires.NotNull(affectedMethod, () => affectedMethod);
			}

			/// <summary>
			///     Sets the <paramref name="occurrencePattern" /> that affects the fault.
			/// </summary>
			/// <param name="occurrencePattern">The occurrence pattern that should be set.</param>
			public void WithOccurrencePattern(OccurrencePattern occurrencePattern)
			{
				Requires.NotNull(occurrencePattern, () => occurrencePattern);
				_occurrencePattern = MetadataBuilders.GetBuilder(occurrencePattern).RegisterMetadata(_fault);
			}

			/// <summary>
			///     Creates an immutable <see cref="FaultInfo" /> instance from the current state of the builder and makes it available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			/// <param name="component">The component that is affected by the fault.</param>
			internal FaultInfo RegisterMetadata(Component component)
			{
				Requires.NotNull(component, () => component);

				var info = new FaultInfo(component, _fault);
				MetadataProvider.FinalizeMetadata(_fault, info);

				return info;
			}
		}
	}
}