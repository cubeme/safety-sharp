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
	using Utilities;

	public partial class Component : IFreezable
	{
		/// <summary>
		///     Maps a field of the current component instance to its set of initial values.
		/// </summary>
		private readonly Dictionary<string, ImmutableArray<object>> _fields = new Dictionary<string, ImmutableArray<object>>();

		/// <summary>
		///     Gets the name of the component instance or <c>null</c> if no name could be determined.
		/// </summary>
		internal string Name { get; private set; }

		/// <summary>
		///     Gets the <see cref="Component" /> instances that are direct sub components of the current instance.
		/// </summary>
		internal IEnumerable<Component> SubComponents
		{
			get
			{
				Assert.IsFrozen(this);
				return GetType()
					.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
					.Where(field => typeof(IComponent).IsAssignableFrom(field.FieldType))
					.Select(field => field.GetValue(this) as Component)
					.Where(component => component != null);
			}
		}

		/// <summary>
		///     Gets a value indicating whether the current instance is frozen, indicating that the instance does not allow any further
		///     state modifications.
		/// </summary>
		public bool IsFrozen { get; private set; }

		/// <summary>
		///     Marks the current instance as frozen, disallowing any further state modifications.
		/// </summary>
		public void Freeze()
		{
			Assert.IsNotFrozen(this);
			IsFrozen = true;
		}

		/// <summary>
		///     Gets the sub component with the given name.
		/// </summary>
		/// <param name="name">The name of the sub component that should be returned.</param>
		internal Component GetSubComponent(string name)
		{
			Argument.NotNullOrWhitespace(name, () => name);
			Assert.IsFrozen(this);

			var field = GetType().GetField(name, BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic);
			Argument.Satisfies(field != null, () => name, "A sub component with name '{0}' does not exist.", name);

			if (!typeof(IComponent).IsAssignableFrom(field.FieldType))
				Argument.Satisfies(false, () => name, "The field with name '{0}' is not a sub component.", name);

			var component = field.GetValue(this) as Component;
			Assert.NotNull(component);
			return component;
		}

		/// <summary>
		///     Gets the initial values of the field with name <paramref name="fieldName" />.
		/// </summary>
		/// <param name="fieldName">The name of the field the initial values should be returned for.</param>
		internal ImmutableArray<object> GetInitialValuesOfField(string fieldName)
		{
			Argument.NotNullOrWhitespace(fieldName, () => fieldName);
			Assert.IsFrozen(this);

			ImmutableArray<object> initialValues;
			if (!_fields.TryGetValue(fieldName, out initialValues))
				Argument.Satisfies(false, () => fieldName, "A field with name '{0}' does not exist.", fieldName);

			return initialValues;
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

		/// <summary>
		///     Adds metadata about a field of the component to the <see cref="Component" /> instance.
		/// </summary>
		/// <param name="field">An expression of the form <c>() => field</c> that referes to a field of the component.</param>
		/// <param name="initialValues">The initial values of the field.</param>
		protected void SetInitialValues<T>(Expression<Func<T>> field, params T[] initialValues)
		{
			Argument.NotNull(field, () => field);
			Argument.NotNull(initialValues, () => initialValues);
			Argument.Satisfies(initialValues.Length > 0, () => initialValues, "At least one value must be provided.");
			Argument.OfType<MemberExpression>(field.Body, () => field, "Expected a lambda expression of the form '() => field'.");
			Assert.IsNotFrozen(this);

			var fieldInfo = ((MemberExpression)field.Body).Member as FieldInfo;
			Argument.Satisfies(fieldInfo != null, () => field, "Expected a lambda expression of the form '() => field'.");

			_fields[fieldInfo.Name] = initialValues.Cast<object>().ToImmutableArray();
		}
	}
}