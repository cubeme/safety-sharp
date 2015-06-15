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
	using Modeling.Faults;
	using Utilities;

	partial class FaultMetadata
	{
		/// <summary>
		///     Represents a mutable builder for <see cref="FaultMetadata" /> instances.
		/// </summary>
		public class Builder
		{
			private readonly Fault _fault;
			private readonly List<FaultEffectMetadata> _faultEffects = new List<FaultEffectMetadata>();
			private readonly FieldCollectionBuilder _fields;
			private readonly List<StepMethodMetadata> _stepMethods = new List<StepMethodMetadata>();
			private OccurrencePatternMetadata _occurrencePattern;

			/// <summary>
			///     Initializes a new instance.
			/// </summary>
			/// <param name="fault">The fault instance the metadata should be built for.</param>
			internal Builder(Fault fault)
			{
				Requires.NotNull(fault, () => fault);

				_fault = fault;
				_fields = new FieldCollectionBuilder(fault);
			}

			/// <summary>
			///     Adds the <paramref name="field" /> to the fault's metadata.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithField(FieldInfo field)
			{
				_fields.WithField(field);
			}

			/// <summary>
			///     Adds the <paramref name="field" /> of compile-time generic type to the fault's metadata. The field
			///     is not added if it is not of a supported field type.
			/// </summary>
			/// <param name="field">The field that should be added to the metadata.</param>
			public void WithGenericField(FieldInfo field)
			{
				_fields.WithGenericField(field);
			}

			/// <summary>
			///     Sets the initial <paramref name="values" /> of the fault's <paramref name="field" />.
			/// </summary>
			/// <param name="field">The field whose initial values should be set.</param>
			/// <param name="values">The initial values of the field.</param>
			public void WithInitialValues(FieldInfo field, params object[] values)
			{
				_fields.WithInitialValues(field, values);
			}

			/// <summary>
			///     Adds the <paramref name="faultEffect" /> to the fault's metadata.
			/// </summary>
			/// <param name="faultEffect">The fault effect that should be added.</param>
			/// <param name="affectedMethod">The affected method of the affected component.</param>
			public void WithFaultEffect(MethodInfo faultEffect, MethodInfo affectedMethod)
			{
				Requires.NotNull(faultEffect, () => faultEffect);
				Requires.NotNull(affectedMethod, () => affectedMethod);

				_faultEffects.Add(new FaultEffectMetadata(_fault, faultEffect, affectedMethod));
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
			///     Adds the <paramref name="stepMethod" /> to the component's metadata. If <paramref name="stepMethod" /> overrides a step
			///     method declared by a base type, the <paramref name="baseStepMethod" /> must not be <c>null</c>.
			/// </summary>
			/// <param name="stepMethod">The method representing the component's behavior that should be added to the component's metadata.</param>
			/// <param name="baseStepMethod">The overridden behavior of the base type, if any.</param>
			public void WithStepMethod(MethodInfo stepMethod, MethodInfo baseStepMethod = null)
			{
				Requires.NotNull(stepMethod, () => stepMethod);
				Requires.That(baseStepMethod == null || _stepMethods.Any(b => b.Method == baseStepMethod), () => baseStepMethod,
					"The base step method is unknown.");

				var metadata = new StepMethodMetadata(_fault, stepMethod, baseStepMethod);
				Requires.That(!metadata.CanBeAffectedByFaultEffects, () => stepMethod, "Fault step methods must be sensitive to fault effects.");

				_stepMethods.Add(metadata);
			}

			/// <summary>
			///     Creates an immutable <see cref="FaultMetadata" /> instance from the current state of the builder and makes it available
			///     to S#'s <see cref="MetadataProvider" />.
			/// </summary>
			/// <param name="component">The component that is affected by the fault.</param>
			internal FaultMetadata RegisterMetadata(Component component)
			{
				Requires.NotNull(component, () => component);

				var metadata = new FaultMetadata
				{
					_component = component,
					Fault = _fault,
					FaultEffects = new MemberCollection<FaultEffectMetadata>(_fault, _faultEffects),
					Fields = _fields.ToImmutableCollection(),
					StepMethods = new MemberCollection<StepMethodMetadata>(_fault, _stepMethods),
					OccurrencePattern = _occurrencePattern
				};

				MetadataProvider.FinalizeMetadata(_fault, metadata);
				return metadata;
			}
		}
	}
}