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

	public abstract class Component : IComponent, IIsImmutable
	{
		/// <summary>
		///     Maps a field of the current component instance to its set of initial values.
		/// </summary>
		private readonly Dictionary<string, ImmutableArray<object>> _fields = new Dictionary<string, ImmutableArray<object>>();

		/// <summary>
		///     The name of the component instance.
		/// </summary>
		private string _name;

		/// <summary>
		///     The sub components of the component.
		/// </summary>
		private ImmutableArray<Component> _subComponents;

		/// <summary>
		///     Gets or sets the name of the component instance. Returns <c>null</c> if no component name could be determined.
		/// </summary>
		internal string Name
		{
			get
			{
				Requires.IsImmutable(this);
				return _name;
			}
		}

		/// <summary>
		///     Gets the <see cref="Component" /> instances that are direct sub components of the current instance.
		/// </summary>
		internal ImmutableArray<Component> SubComponents
		{
			get
			{
				Requires.IsImmutable(this);
				return _subComponents;
			}
		}

		/// <summary>
		///     Gets a value indicating whether the component is sealed and can no longer be modified.
		/// </summary>
		public bool IsImmutable { get; private set; }

		/// <summary>
		///     Allows access to a non-public member of the component.
		/// </summary>
		/// <typeparam name="T">The type of the accessed member.</typeparam>
		/// <param name="memberName">The name of the member that should be accessed.</param>
		/// <returns>Returns an <see cref="InternalAccess{T}" /> instance that can be used to access the non-public member.</returns>
		public InternalAccess<T> AccessInternal<T>(string memberName)
		{
			return new InternalAccess<T>(this, memberName);
		}

		/// <summary>
		///     Adds metadata about a field of the component to the <see cref="Component" /> instance.
		/// </summary>
		/// <param name="field">An expression of the form <c>() => field</c> that referes to a field of the component.</param>
		/// <param name="initialValues">The initial values of the field.</param>
		protected void SetInitialValues<T>(Expression<Func<T>> field, params T[] initialValues)
		{
			Requires.NotNull(field, () => field);
			Requires.NotNull(initialValues, () => initialValues);
			Requires.ArgumentSatisfies(initialValues.Length > 0, () => initialValues, "At least one value must be provided.");
			Requires.OfType<MemberExpression>(field.Body, () => field, "Expected a lambda expression of the form '() => field'.");
			Requires.NotImmutable(this);

			var fieldInfo = ((MemberExpression)field.Body).Member as FieldInfo;
			Requires.ArgumentSatisfies(fieldInfo != null, () => field, "Expected a lambda expression of the form '() => field'.");

			_fields[fieldInfo.Name] = initialValues.Cast<object>().ToImmutableArray();

			var random = new Random();
			fieldInfo.SetValue(this, initialValues[random.Next(0, initialValues.Length)]);
		}

		/// <summary>
		///     Gets the initial values of the field with name <paramref name="fieldName" />.
		/// </summary>
		/// <param name="fieldName">The name of the field the initial values should be returned for.</param>
		internal ImmutableArray<object> GetInitialValuesOfField(string fieldName)
		{
			Requires.NotNullOrWhitespace(fieldName, () => fieldName);
			Requires.IsImmutable(this);

			ImmutableArray<object> initialValues;
			if (!_fields.TryGetValue(fieldName, out initialValues))
				Requires.ArgumentSatisfies(false, () => fieldName, "A field with name '{0}' does not exist.", fieldName);

			return initialValues;
		}

		/// <summary>
		///     Gets the sub component with the given name.
		/// </summary>
		/// <param name="name">The name of the sub component that should be returned.</param>
		internal Component GetSubComponent(string name)
		{
			Requires.NotNullOrWhitespace(name, () => name);
			Requires.IsImmutable(this);

			var subComponent = SubComponents.SingleOrDefault(c => c.Name == name);
			Requires.ArgumentSatisfies(subComponent != null, () => name, "A sub component with name '{0}' does not exist.", name);

			return subComponent;
		}

		/// <summary>
		///     Marks the component as immutable, disallowing any future state modifications.
		/// </summary>
		/// <param name="componentName">The name of the component or <c>null</c> if no name can be determined.</param>
		internal void ToImmutable(string componentName = null)
		{
			Requires.NotImmutable(this);

			var subComponents =
				from field in GetType().GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
				where typeof(IComponent).IsAssignableFrom(field.FieldType)
				let component = field.GetValue(this) as Component
				where component != null
				select new { field.Name, Component = component };

			var fieldsWithDeterministicInitialValue =
				from field in GetType().GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic)
				where !typeof(IComponent).IsAssignableFrom(field.FieldType) && !_fields.ContainsKey(field.Name)
				let value = field.GetValue(this)
				select new { field.Name, Values = ImmutableArray.Create(value) };

			foreach (var field in fieldsWithDeterministicInitialValue)
				_fields.Add(field.Name, field.Values);

			IsImmutable = true;
			_name = componentName;
			_subComponents = subComponents.Select(subComponent =>
			{
				subComponent.Component.ToImmutable(subComponent.Name);
				return subComponent.Component;
			}).ToImmutableArray();
		}

		protected static void Choose<T>(out T result, T value1, T value2, params T[] values)
		{
			throw new NotImplementedException();
		}

		protected static void ChooseFromRange(out int result, int inclusiveLowerBound, int inclusiveUpperBound)
		{
			throw new NotImplementedException();
		}

		protected static void ChooseFromRange(out decimal result, decimal inclusiveLowerBound, decimal inclusiveUpperBound)
		{
			throw new NotImplementedException();
		}

		protected static T Choose<T>()
			where T : struct
		{
			throw new NotSupportedException();
		}

		protected static T Choose<T>(T value1, T value2, params T[] values)
		{
			throw new NotSupportedException();
		}

		protected static int ChooseFromRange(int inclusiveLowerBound, int inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}

		protected static decimal ChooseFromRange(decimal inclusiveLowerBound, decimal inclusiveUpperBound)
		{
			throw new NotSupportedException();
		}

		protected virtual void Update()
		{
			throw new NotSupportedException();
		}
	}
}