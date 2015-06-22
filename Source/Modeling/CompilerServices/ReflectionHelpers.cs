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

namespace SafetySharp.CompilerServices
{
	using System;
	using System.Linq;
	using System.Reflection;
	using Modeling;
	using Modeling.Faults;
	using Runtime;
	using Utilities;

	/// <summary>
	///     Provides helper methods for reflection scenarios.
	/// </summary>
	public static class ReflectionHelpers
	{
		private const BindingFlags Flags = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.DeclaredOnly;

		/// <summary>
		///     Gets the instance field called <paramref name="fieldName" /> of type <paramref name="fieldType" /> declared by the
		///     <paramref name="declaringType" />.
		/// </summary>
		/// <param name="declaringType">The type that declares the field.</param>
		/// <param name="fieldType">The type of the field.</param>
		/// <param name="fieldName">The name of the field.</param>
		public static FieldInfo GetField(Type declaringType, Type fieldType, string fieldName)
		{
			Requires.NotNull(declaringType, () => declaringType);
			Requires.NotNull(fieldType, () => fieldType);
			Requires.NotNullOrWhitespace(fieldName, () => fieldName);

			var field = declaringType
				.GetFields(Flags)
				.SingleOrDefault(f => f.Name == fieldName && f.FieldType == fieldType);

			Requires.That(field != null, () => fieldName,
				"'{0}' does not declare an instance field called '{1}' of type '{2}'.",
				declaringType.FullName, fieldName, fieldType);

			return field;
		}

		/// <summary>
		///     Gets the instance property called <paramref name="propertyName" /> of type <paramref name="propertyType" /> declared by
		///     the <paramref name="declaringType" />.
		/// </summary>
		/// <param name="declaringType">The type that declares the property.</param>
		/// <param name="propertyType">The type of the property.</param>
		/// <param name="propertyName">The name of the property.</param>
		public static PropertyInfo GetProperty(Type declaringType, Type propertyType, string propertyName)
		{
			Requires.NotNull(declaringType, () => declaringType);
			Requires.NotNull(propertyType, () => propertyType);
			Requires.NotNullOrWhitespace(propertyName, () => propertyName);

			var property = declaringType
				.GetProperties(Flags)
				.SingleOrDefault(p => p.Name == propertyName && p.PropertyType == propertyType);

			Requires.That(property != null, () => propertyName,
				"'{0}' does not declare an instance property called '{1}' of type '{2}'.",
				declaringType.FullName, propertyName, propertyType);

			return property;
		}

		/// <summary>
		///     Gets the instance method called <paramref name="methodName" /> declared by the <paramref name="declaringType" />,
		///     with the signature of the method defined by the <paramref name="argumentTypes" /> and <paramref name="returnType" />.
		/// </summary>
		/// <param name="declaringType">The type that declares the method.</param>
		/// <param name="methodName">The name of the method.</param>
		/// <param name="argumentTypes">The argument types of the method.</param>
		/// <param name="returnType">The return type of the method.</param>
		public static MethodInfo GetMethod(Type declaringType, string methodName, Type[] argumentTypes, Type returnType)
		{
			Requires.NotNull(declaringType, () => declaringType);
			Requires.NotNullOrWhitespace(methodName, () => methodName);
			Requires.NotNull(argumentTypes, () => argumentTypes);
			Requires.NotNull(returnType, () => returnType);

			var method = declaringType
				.GetMethods(Flags)
				.SingleOrDefault(m =>
					m.Name == methodName &&
					m.ReturnType == returnType &&
					m.GetParameters().Select(p => p.ParameterType).SequenceEqual(argumentTypes));

			Requires.That(method != null, "'{0}' does not declare an instance method called '{1}' with the given signature.",
				declaringType.FullName, methodName);

			return method;
		}

		/// <summary>
		///     Gets the <paramref name="component" />'s <see cref="FieldMetadata" /> for the <paramref name="field" />.
		/// </summary>
		/// <param name="component">The component instance the metadata should be returned for.</param>
		/// <param name="field">The field the metadata should be returned for.</param>
		public static FieldMetadata GetFieldMetadata(IComponent component, FieldInfo field)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(field, () => field);
			Requires.OfType<Component>(component, () => component);

			return GetFieldMetadata((Component)component, field);
		}

		/// <summary>
		///     Gets the <paramref name="component" />'s <see cref="FieldMetadata" /> for the <paramref name="field" />.
		/// </summary>
		/// <param name="component">The component instance the metadata should be returned for.</param>
		/// <param name="field">The field the metadata should be returned for.</param>
		public static FieldMetadata GetFieldMetadata(Component component, FieldInfo field)
		{
			Requires.NotNull(component, () => component);
			Requires.NotNull(field, () => field);

			var fieldMetadata = component.Metadata.Fields.SingleOrDefault(f => f.FieldInfo == field);
			Requires.That(fieldMetadata != null, () => field, "The component does not declare the given field.");

			return fieldMetadata;
		}

		/// <summary>
		///     Gets the <paramref name="fault" />'s <see cref="FieldMetadata" /> for the <paramref name="field" />.
		/// </summary>
		/// <param name="fault">The fault instance the metadata should be returned for.</param>
		/// <param name="field">The field the metadata should be returned for.</param>
		public static FieldMetadata GetFieldMetadata(Fault fault, FieldInfo field)
		{
			Requires.NotNull(fault, () => fault);
			Requires.NotNull(field, () => field);

			var fieldMetadata = fault.Metadata.Fields.SingleOrDefault(f => f.FieldInfo == field);
			Requires.That(fieldMetadata != null, () => field, "The fault does not declare the given field.");

			return fieldMetadata;
		}

		/// <summary>
		///     Gets the <paramref name="occurrencePattern" />'s <see cref="FieldMetadata" /> for the <paramref name="field" />.
		/// </summary>
		/// <param name="occurrencePattern">The occurrence pattern instance the metadata should be returned for.</param>
		/// <param name="field">The field the metadata should be returned for.</param>
		public static FieldMetadata GetFieldMetadata(OccurrencePattern occurrencePattern, FieldInfo field)
		{
			Requires.NotNull(occurrencePattern, () => occurrencePattern);
			Requires.NotNull(field, () => field);

			var fieldMetadata = occurrencePattern.Metadata.Fields.SingleOrDefault(f => f.FieldInfo == field);
			Requires.That(fieldMetadata != null, () => field, "The occurrence pattern does not declare the given field.");

			return fieldMetadata;
		}
	}
}