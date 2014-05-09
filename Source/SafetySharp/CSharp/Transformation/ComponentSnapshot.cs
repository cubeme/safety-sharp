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

			Component = component;
			Name = name;
			SubComponents = subComponents;
			_fieldValues = fieldValues;
		}

		/// <summary>
		///     Gets the <see cref="Component" /> instance the snapshot was created from.
		/// </summary>
		internal Component Component { get; private set; }

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
	}
}