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

namespace SafetySharp.Runtime.Analysis
{
	using System;
	using System.Reflection;
	using Modeling;
	using Utilities;

	/// <summary>
	///     Provides access to a non-public member of a component.
	/// </summary>
	/// <typeparam name="T">The type of the accessed member.</typeparam>
	public class MemberAccess<T> : IMemberAccess
	{
		/// <summary>
		///     The reflection information of the accessed field.
		/// </summary>
		private readonly FieldInfo _fieldInfo;

		/// <summary>
		///     The reflection information of the accessed property.
		/// </summary>
		private readonly PropertyInfo _propertyInfo;

		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="component">The component instance that should be accessed.</param>
		/// <param name="memberName">The name of the accessed field or property getter that should be accessed.</param>
		internal MemberAccess(IComponent component, string memberName)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNullOrWhitespace(memberName, () => memberName);

			Component = component;
			MemberName = memberName;

			var componentType = component.GetType();
			var bindingFlags = BindingFlags.Instance | BindingFlags.FlattenHierarchy | BindingFlags.Public | BindingFlags.NonPublic;

			_fieldInfo = componentType.GetField(memberName, bindingFlags);
			_propertyInfo = componentType.GetProperty(memberName, bindingFlags);

			Requires.That(_fieldInfo != null || _propertyInfo != null,
				"Component of type '{0}' has no member with name '{1}'.", componentType.FullName, memberName);

			Requires.That(_propertyInfo == null || _propertyInfo.CanRead,
				"Property '{0}.{1}' is write-only.", componentType.FullName, memberName);

			var memberType = _fieldInfo == null ? _propertyInfo.PropertyType : _fieldInfo.FieldType;
			Requires.That(memberType == typeof(T),
				"Expected '{0}.{1}' to be of type '{2}', but actual type is '{3}'.",
				componentType.FullName, memberName, memberType.FullName, typeof(T).FullName);
		}

		/// Gets the current value of the accessed memb
		internal T Value
		{
			get
			{
				if (_fieldInfo != null)
					return (T)_fieldInfo.GetValue(Component);

				return (T)_propertyInfo.GetValue(Component);
			}
		}

		/// <summary>
		///     Gets the component instance that is accessed.
		/// </summary>
		public IComponent Component { get; private set; }

		/// <summary>
		///     Gets the name of the accessed field or property getter.
		/// </summary>
		public string MemberName { get; private set; }

		/// <summary>
		///     Gets the current value of the accessed member.
		/// </summary>
		/// <param name="memberAccess">The member access the value should be retrieved for.</param>
		public static implicit operator T(MemberAccess<T> memberAccess)
		{
			return memberAccess.Value;
		}
	}
}