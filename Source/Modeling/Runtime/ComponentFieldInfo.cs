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
	using System.Collections.Immutable;
	using System.Reflection;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a S# <see cref="Component" /> instance field.
	/// </summary>
	public sealed class ComponentFieldInfo
	{
		/// <summary>
		///     The component the field belongs to.
		/// </summary>
		private readonly Component _component;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component the field belongs to.</param>
		/// <param name="field">The field that represents the component field.</param>
		/// <param name="initialValues">
		///     The set of initial values. <c>null</c> indicates that the current field value should be used instead.
		/// </param>
		internal ComponentFieldInfo(Component component, FieldInfo field, object[] initialValues)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(field, () => field);

			_component = component;

			Field = field;
			InitialValues = initialValues == null ? ImmutableArray.Create(field.GetValue(component)) : initialValues.ToImmutableArray();
		}

		/// <summary>
		///     Gets the underlying .NET field.
		/// </summary>
		public FieldInfo Field { get; private set; }

		/// <summary>
		///     Gets the name of the field.
		/// </summary>
		public string Name
		{
			get { return Field.Name; }
		}

		/// <summary>
		///     Gets the metadata of the component the field belongs to.
		/// </summary>
		public ComponentInfo Component
		{
			get { return _component.GetComponentInfo(); }
		}

		/// <summary>
		///     Gets the type of the field.
		/// </summary>
		public Type Type
		{
			get { return Field.FieldType; }
		}

		/// <summary>
		///     Gets the field's set of initial values.
		/// </summary>
		public ImmutableArray<object> InitialValues { get; private set; }

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("{0} {1} = {2}", Type.FullName, Name, String.Join(", ", InitialValues));
		}
	}
}