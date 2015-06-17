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
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents a class that can be used to build up <see cref="MemberCollection{FieldMetadata}" /> instances.
	/// </summary>
	internal sealed class FieldCollectionBuilder
	{
		private readonly Dictionary<FieldInfo, object[]> _fields = new Dictionary<FieldInfo, object[]>();
		private readonly IMetadataObject _object;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="obj">The objects that declares the fields.</param>
		public FieldCollectionBuilder(IMetadataObject obj)
		{
			Requires.NotNull(obj, () => obj);
			_object = obj;
		}

		/// <summary>
		///     Adds the <paramref name="field" /> to the component's metadata.
		/// </summary>
		/// <param name="field">The field that should be added to the metadata.</param>
		public void WithField(FieldInfo field)
		{
			Requires.NotNull(field, () => field);
			Requires.That(!_fields.ContainsKey(field), () => field, "The field has already been added.");
			Requires.That(field.FieldType == typeof(int) || field.FieldType == typeof(bool) ||
						  field.FieldType == typeof(double) || field.FieldType.IsEnum, () => field,
				"Invalid field type: Only 'bool', 'int', 'double', and enumeration types are supported.");

			_fields.Add(field, null);
		}

		/// <summary>
		///     Adds the <paramref name="field" /> of compile-time generic type to the component's metadata. The field
		///     is not added if it is not of a supported field type.
		/// </summary>
		/// <param name="field">The field that should be added to the metadata.</param>
		public void WithGenericField(FieldInfo field)
		{
			Requires.NotNull(field, () => field);
			Requires.That(!_fields.ContainsKey(field), () => field, "The field has already been added.");

			if (field.FieldType == typeof(int) || field.FieldType == typeof(bool) || field.FieldType == typeof(double) || field.FieldType.IsEnum)
				WithField(field);
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the component's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		public void WithInitialValues(FieldInfo field, object[] values)
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
		///     Returns an immutable <see cref="MemberCollection{FieldMetadata}" /> instance containing all of the fields.
		/// </summary>
		public MemberCollection<FieldMetadata> ToImmutableCollection()
		{
			var fields = _fields.Select(field => new FieldMetadata(_object, field.Key, field.Value));
			return new MemberCollection<FieldMetadata>(_object, fields);
		}
	}
}