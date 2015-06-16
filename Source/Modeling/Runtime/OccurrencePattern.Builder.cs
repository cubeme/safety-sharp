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
	using System.Linq.Expressions;
	using System.Reflection;
	using Modeling.Faults;
	using Utilities;

	partial class OccurrencePatternMetadata
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="OccurrencePatternMetadata" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly FieldCollectionBuilder _fields;
			private readonly OccurrencePattern _occurrencePattern;
			private readonly List<StepMethodMetadata> _stepMethods = new List<StepMethodMetadata>();

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="occurrencePattern">The occurrence pattern the metadata should be built for.</param>
			internal Builder(OccurrencePattern occurrencePattern)
			{
				Requires.NotNull(occurrencePattern, () => occurrencePattern);

				_occurrencePattern = occurrencePattern;
				_fields = new FieldCollectionBuilder(occurrencePattern);
			}

			/// <summary>
			///     Adds the <paramref name="field" /> to the occurrence pattern's metadata.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithField(FieldInfo field)
			{
				_fields.WithField(field);
			}

			/// <summary>
			///     Adds the <paramref name="field" /> of compile-time generic type to the occurrence pattern's metadata. The field
			///     is not added if it is not of a supported field type.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithGenericField(FieldInfo field)
			{
				_fields.WithGenericField(field);
			}

			/// <summary>
			///     Sets the initial <paramref name="values" /> of the occurrence pattern's <paramref name="field" />.
			/// </summary>
			/// <param name="field">The field whose initial values should be set.</param>
			/// <param name="values">The initial values of the field.</param>
			public void WithInitialValues(FieldInfo field, params object[] values)
			{
				_fields.WithInitialValues(field, values);
			}

			/// <summary>
			///     Adds the <paramref name="stepMethod" /> to the occurrence pattern's metadata. If <paramref name="stepMethod" />
			///     overrides a step method declared by a base type, the <paramref name="baseStepMethod" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="stepMethod">
			///     The method representing the occurrence pattern's step method that should be added to the occurrence
			///     pattern's metadata.
			/// </param>
			/// <param name="baseStepMethod">The overridden step method of the base type, if any.</param>
			public void WithStepMethod(MethodInfo stepMethod, MethodInfo baseStepMethod = null)
			{
				Requires.NotNull(stepMethod, () => stepMethod);
				Requires.That(baseStepMethod == null || _stepMethods.Any(method => method.MethodInfo == baseStepMethod), () => baseStepMethod,
					"The base step method is unknown.");

				var baseMetadata = baseStepMethod != null ? _stepMethods.Single(method => method.MethodInfo == baseStepMethod) : null;
				var metadata = new StepMethodMetadata(_occurrencePattern, stepMethod, baseMetadata);

				Requires.That(!metadata.CanBeAffectedByFaultEffects, () => stepMethod,
					"Occurrence pattern step methods must not be sensitive to fault effects.");

				_stepMethods.Add(metadata);
			}

			/// <summary>
			///     Creates an immutable <see cref="OccurrencePatternMetadata" /> instance from the current state of the builder and makes
			///     it
			///     available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			/// <param name="fault">The fault that is affected by the occurrence pattern.</param>
			internal OccurrencePatternMetadata RegisterMetadata(Fault fault)
			{
				Requires.NotNull(fault, () => fault);

				var metadata = new OccurrencePatternMetadata
				{
					_fault = fault,
					OccurrencePattern = _occurrencePattern,
					Fields = _fields.ToImmutableCollection(),
					StepMethods = new MemberCollection<StepMethodMetadata>(_occurrencePattern, _stepMethods)
				};

				MetadataProvider.FinalizeMetadata(_occurrencePattern, metadata);
				return metadata;
			}
		}
	}
}