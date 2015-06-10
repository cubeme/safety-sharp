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
	using System.Reflection;
	using Utilities;

	/// <summary>
	///     When applied to a port, indicates the field that the S# compiler used to implement the port.
	/// </summary>
	[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property, AllowMultiple = false, Inherited = false)]
	public sealed class BackingFieldAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="fieldName">The name of the marked port's backing field.</param>
		public BackingFieldAttribute(string fieldName)
		{
			Requires.NotNullOrWhitespace(fieldName, () => fieldName);
			FieldName = fieldName;
		}

		/// <summary>
		///     Gets the name of the marked port's backing field.
		/// </summary>
		public string FieldName { get; private set; }

		/// <summary>
		///     Gets the <see cref="FieldInfo" /> object representing the marked port's backing field.
		/// </summary>
		/// <param name="type">The type that declares the marked port.</param>
		public FieldInfo GetFieldInfo(Type type)
		{
			Requires.NotNull(type, () => type);

			var field = type.GetField(FieldName, BindingFlags.DeclaredOnly | BindingFlags.Instance | BindingFlags.NonPublic);
			Requires.That(field != null, "Unable to find backing field '{0}.{1}'.", type.FullName, FieldName);

			return field;
		}
	}
}