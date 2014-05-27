// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
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

namespace SafetySharp.Metamodel
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Utilities;

	/// <summary>
	///     Resolves metamodel element references.
	/// </summary>
	internal class MetamodelResolver
	{
		/// <summary>
		///     The empty metamodel resolver that cannot resolve any references.
		/// </summary>
		internal static readonly MetamodelResolver Empty = new MetamodelResolver
		{
			_referenceMap = ImmutableDictionary<IMetamodelReference, MetamodelElement>.Empty
		};

		/// <summary>
		///     Maps metamodel references to metamodel elements.
		/// </summary>
		private ImmutableDictionary<IMetamodelReference, MetamodelElement> _referenceMap;

		/// <summary>
		///     Initializes a new instance of the <see cref="MetamodelResolver" /> type.
		/// </summary>
		private MetamodelResolver()
		{
		}

		/// <summary>
		///     Resolves the metamodel <paramref name="reference" /> to the actual <see cref="MetamodelElement" /> instance.
		/// </summary>
		/// <typeparam name="T">The type of the referenced <see cref="MetamodelElement" />.</typeparam>
		/// <param name="reference">The reference that should be resolved.</param>
		public T Resolve<T>(IMetamodelReference<T> reference)
			where T : MetamodelElement
		{
			Argument.NotNull(reference, () => reference);
			Argument.Satisfies(_referenceMap.ContainsKey(reference), () => reference, "The given reference is unknown.");

			var element = _referenceMap[reference];
			Assert.OfType<T>(element, "Metamodel reference of type '{0}' refers to a metamodel element of type '{1}'.",
							 typeof(MetamodelReference<T>).FullName, element.GetType().FullName);

			return (T)element;
		}

		/// <summary>
		///     Creates a copy of the <see cref="MetamodelResolver" /> that can resolve <paramref name="reference" /> to
		///     <paramref name="referencedElement" />.
		/// </summary>
		/// <param name="reference">The reference that should be added to the resolver.</param>
		/// <param name="referencedElement">The referenced metamodel element that <paramref name="reference" /> refers to.</param>
		internal MetamodelResolver With(IMetamodelReference reference, MetamodelElement referencedElement)
		{
			Argument.NotNull(reference, () => reference);
			Argument.NotNull(referencedElement, () => referencedElement);
			Argument.Satisfies(!_referenceMap.ContainsKey(reference), () => reference,
							   "The given reference has already been added to the resolver.");
			Argument.Satisfies(reference.GetType().GetGenericTypeDefinition() == typeof(MetamodelReference<>) &&
							   reference.GetType().GetGenericArguments().Count() == 1 &&
							   reference.GetType().GetGenericArguments().Single() == referencedElement.GetType(),
							   () => reference,
							   "The given reference is of type '{0}' and cannot reference a metamodel element of type '{1}'.",
							   reference.GetType().FullName, referencedElement.GetType().FullName);

			return new MetamodelResolver { _referenceMap = _referenceMap.Add(reference, referencedElement) };
		}
	}
}