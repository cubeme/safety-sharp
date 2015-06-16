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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Diagnostics;
	using System.Globalization;
	using System.Linq;
	using System.Linq.Expressions;
	using System.Reflection;
	using Utilities;

	partial class Component
	{
		/// <summary>
		///     Maps each field of the component to its set of initial values.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private readonly Dictionary<FieldInfo, object[]> _fields = new Dictionary<FieldInfo, object[]>();

		/// <summary>
		///     Maps each field of the component to its set of initial values after initialization.
		/// </summary>
		[DebuggerBrowsable(DebuggerBrowsableState.Never)]
		private Dictionary<FieldInfo, object[]> _initializedFields;

		/// <summary>
		///     Gets the fields of the component, including their set of initial values.
		/// </summary>
		internal Dictionary<FieldInfo, object[]> Fields
		{
			get
			{
				RequiresIsSealed();
				return _initializedFields;
			}
		}

		/// <summary>
		///     Sets the initial <paramref name="values" /> of the component's <paramref name="field" />.
		/// </summary>
		/// <param name="field">The field whose initial values should be set.</param>
		/// <param name="values">The initial values of the field.</param>
		public void SetInitialValues<T>(Expression<Func<T>> field, params T[] values)
		{
			Requires.NotNull(field, () => field);
			Requires.NotNull(values, () => values);
			Requires.That(values.Length > 0, () => values, "At least one value must be provided.");
			Requires.That(field.Body is MemberExpression, () => field, "Expected a reference to a field of the component.");
			RequiresNotSealed();

			// Check that we really deal with a field and that this field is actually declared or inherited by the component
			var fieldInfo = ((MemberExpression)field.Body).Member as FieldInfo;
			Requires.That(fieldInfo != null, () => field, "Expected a reference to a field of the component.");
			Requires.That(fieldInfo.DeclaringType.IsInstanceOfType(this), () => field, "Expected a reference to a field of the component.");

			// Check for undefined enum values
			if (fieldInfo.FieldType.IsEnum)
			{
				var invalidValues = values.Where(value => !Enum.IsDefined(fieldInfo.FieldType, value)).ToArray();
				if (invalidValues.Length != 0)
					Requires.That(false, () => values, "A value of '{0}' is not defined by '{1}'.", invalidValues[0], fieldInfo.FieldType.FullName);

				_fields[fieldInfo] = values.Select(value => (object)((IConvertible)value).ToInt32(CultureInfo.InvariantCulture)).ToArray();
			}
			else
				_fields[fieldInfo] = values.Cast<object>().ToArray();

			var random = new Random();
			fieldInfo.SetValue(this, values[random.Next(0, values.Length)]);
		}

		/// <summary>
		///     Initializes the fields of the component.
		/// </summary>
		private void InitializeFields()
		{
			var fields = GetType()
				.GetFields(typeof(Component))
				.Where(field =>
					!field.IsStatic && !typeof(IComponent).IsAssignableFrom(field.FieldType) && !_fields.ContainsKey(field) &&
					(field.FieldType.IsEnum || field.FieldType == typeof(int) || field.FieldType == typeof(bool) || field.FieldType == typeof(double)));

			foreach (var field in fields)
			{
				object value;
				if (field.FieldType.IsEnum)
					value = ((IConvertible)field.GetValue(this)).ToInt32(CultureInfo.InvariantCulture);
				else
					value = field.GetValue(this);

				_fields.Add(field, new[] { value });
			}

			_initializedFields = _fields;
		}
	}
}