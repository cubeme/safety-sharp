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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Collections.Immutable;
	using System.Linq;
	using System.Linq.Expressions;
	using System.Reflection;
	using CSharp.Transformation;
	using Utilities;

	public partial class Component
	{
		/// <summary>
		///     Maps a field of the current component instance to its set of initial values.
		/// </summary>
		private readonly Dictionary<string, ImmutableArray<object>> _fields = new Dictionary<string, ImmutableArray<object>>();

		/// <summary>
		///     Gets the <see cref="Component" /> instances that are direct sub components of the current instance.
		/// </summary>
		internal IEnumerable<Component> SubComponents
		{
			get
			{
				return GetType()
					.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
					.Where(field => typeof(IComponent).IsAssignableFrom(field.FieldType))
					.Select(field => field.GetValue(this) as Component)
					.Where(component => component != null);
			}
		}

		/// <summary>
		///     Gets a snapshot of the current component state.
		/// </summary>
		/// <param name="componentName">The name of the component or <c>null</c> if no name can be determined.</param>
		internal ComponentSnapshot GetSnapshot(string componentName = null)
		{
			var subComponents =
				from field in GetType().GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
				where typeof(IComponent).IsAssignableFrom(field.FieldType)
				let component = field.GetValue(this) as Component
				where component != null
				select component.GetSnapshot(field.Name);

			var fieldsWithDeterministicInitialValue =
				from field in GetType().GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
				where !typeof(IComponent).IsAssignableFrom(field.FieldType) && !_fields.ContainsKey(field.Name)
				let value = field.GetValue(this)
				select new KeyValuePair<string, ImmutableArray<object> >(field.Name, ImmutableArray.Create(value));

			var fields = _fields.ToImmutableDictionary().AddRange(fieldsWithDeterministicInitialValue);
			return new ComponentSnapshot(this, componentName, subComponents.ToImmutableArray(), fields);
		}

		/// <summary>
		///     Adds metadata about a field of the component to the <see cref="Component" /> instance.
		/// </summary>
		/// <param name="field">An expression of the form <c>() => field</c> that referes to a field of the component.</param>
		/// <param name="initialValues">The initial values of the field.</param>
		partial void SetInitialValuesInternal<T>(Expression<Func<T>> field, params T[] initialValues)
		{
			Argument.NotNull(field, () => field);
			Argument.NotNull(initialValues, () => initialValues);
			Argument.Satisfies(initialValues.Length > 0, () => initialValues, "At least one value must be provided.");
			Argument.OfType<MemberExpression>(field.Body, () => field, "Expected a lambda expression of the form '() => field'.");

			var fieldInfo = ((MemberExpression)field.Body).Member as FieldInfo;
			Argument.Satisfies(fieldInfo != null, () => field, "Expected a lambda expression of the form '() => field'.");

			_fields[fieldInfo.Name] = initialValues.Cast<object>().ToImmutableArray();

			var random = new Random();
			fieldInfo.SetValue(this, initialValues[random.Next(0, initialValues.Length)]);
		}

		protected static void Choose<T>(out T result, T value1, T value2, params T[] values)
		{
			result = default(T);
		}

		protected static void ChooseFromRange(out int result, int inclusiveLowerBound, int inclusiveUpperBound)
		{
			result = 0;
		}

		protected static void ChooseFromRange(out decimal result, decimal inclusiveLowerBound, decimal inclusiveUpperBound)
		{
			result = 0;
		}
	}
}