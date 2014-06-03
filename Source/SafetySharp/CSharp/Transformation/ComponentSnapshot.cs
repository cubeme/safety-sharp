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

namespace SafetySharp.CSharp.Transformation
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Modeling;
	using Utilities;

	/// <summary>
	///     During model transformation, a <see cref="ComponentSnapshot" /> instance stores an immutable snapshot of the mutable
	///     state of a <see cref="Component" /> instance.
	/// </summary>
	internal class ComponentSnapshot
	{
		/// <summary>
		///     The <see cref="Component" /> instance the snapshot was created from.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     Maps a field of the current component instance to its set of initial values.
		/// </summary>
		private readonly ImmutableDictionary<string, ImmutableArray<object>> _fieldValues;

		/// <summary>
		///     Initializes a new instance of the <see cref="ComponentSnapshot" /> type.
		/// </summary>
		/// <param name="component">The <see cref="Component" /> instance the snapshot is created from.</param>
		/// <param name="name">The name of the component instance or <c>null</c> if no name could be determined.</param>
		/// <param name="subComponents">
		///     The <see cref="ComponentSnapshot" /> instances that are direct sub components of the current instance.
		/// </param>
		/// <param name="fieldValues">Maps a field of the current component instance to its set of initial values.</param>
		internal ComponentSnapshot(Component component, string name, ImmutableArray<ComponentSnapshot> subComponents,
								   ImmutableDictionary<string, ImmutableArray<object>> fieldValues)
		{
			Argument.NotNull(component, () => component);
			Argument.NotNull(fieldValues, () => fieldValues);

			_component = component;
			Name = name;
			SubComponents = subComponents;
			_fieldValues = fieldValues;
		}

		/// <summary>
		///     Gets the type of the component.
		/// </summary>
		internal Type Type
		{
			get { return _component.GetType(); }
		}

		/// <summary>
		///     Gets the name of the component instance or <c>null</c> if no name could be determined.
		/// </summary>
		internal string Name { get; private set; }

		/// <summary>
		///     Gets the <see cref="Component" /> instances that are direct sub components of the current instance.
		/// </summary>
		internal ImmutableArray<ComponentSnapshot> SubComponents { get; private set; }

		/// <summary>
		///     Gets the sub component with the given name.
		/// </summary>
		/// <param name="name">The name of the sub component that should be returned.</param>
		internal ComponentSnapshot GetSubComponent(string name)
		{
			Argument.NotNullOrWhitespace(name, () => name);

			var subComponent = SubComponents.SingleOrDefault(c => c.Name == name);
			Argument.Satisfies(subComponent != null, () => name, "A sub component with name '{0}' does not exist.", name);

			return subComponent;
		}

		/// <summary>
		///     Gets the initial values of the field with name <paramref name="fieldName" />.
		/// </summary>
		/// <param name="fieldName">The name of the field the initial values should be returned for.</param>
		internal ImmutableArray<object> GetInitialValuesOfField(string fieldName)
		{
			Argument.NotNullOrWhitespace(fieldName, () => fieldName);

			ImmutableArray<object> initialValues;
			if (!_fieldValues.TryGetValue(fieldName, out initialValues))
				Argument.Satisfies(false, () => fieldName, "A field with name '{0}' does not exist.", fieldName);

			return initialValues;
		}

		/// <summary>
		///     Determines whether <paramref name="obj" /> is equal to the current instance.
		/// </summary>
		/// <param name="obj">The object to compare with the current instance.</param>
		/// <returns>
		///     <c>true</c> if <paramref name="obj" /> is equal to the current instance; otherwise, <c>false</c>.
		/// </returns>
		public override bool Equals(object obj)
		{
			if (ReferenceEquals(null, obj))
				return false;

			if (ReferenceEquals(this, obj))
				return true;

			if (obj.GetType() != GetType())
				return false;

			return Equals((ComponentSnapshot)obj);
		}

		/// <summary>
		///     Determines whether <paramref name="other" /> is equal to the current instance.
		/// </summary>
		/// <param name="other">The <see cref="ComponentSnapshot" /> to compare with the current instance.</param>
		/// <returns>
		///     <c>true</c> if <paramref name="other" /> is equal to the current instance; otherwise, <c>false</c>.
		/// </returns>
		[UsedImplicitly]
		internal bool Equals(ComponentSnapshot other)
		{
			Argument.NotNull(other, () => other);

			if (_component != other._component)
				return false;

			foreach (var values in _fieldValues)
			{
				ImmutableArray<object> otherValues;
				if (!other._fieldValues.TryGetValue(values.Key, out otherValues) || !values.Value.SequenceEqual(otherValues))
					return false;
			}

			return SubComponents.SequenceEqual(other.SubComponents);
		}

		/// <summary>
		///     Gets the hash code for the current instance.
		/// </summary>
		public override int GetHashCode()
		{
			return _component.GetHashCode();
		}

		/// <summary>
		///     Checks whether <paramref name="left" /> and <paramref name="right" /> are equal.
		/// </summary>
		/// <param name="left">The snapshot on the left hand side of the equality operator.</param>
		/// <param name="right">The snapshot on the right hand side of the equality operator.</param>
		public static bool operator ==(ComponentSnapshot left, ComponentSnapshot right)
		{
			return Equals(left, right);
		}

		/// <summary>
		///     Checks whether <paramref name="left" /> and <paramref name="right" /> are not equal.
		/// </summary>
		/// <param name="left">The snapshot on the left hand side of the inequality operator.</param>
		/// <param name="right">The snapshot on the right hand side of the inequality operator.</param>
		public static bool operator !=(ComponentSnapshot left, ComponentSnapshot right)
		{
			return !Equals(left, right);
		}
	}
}