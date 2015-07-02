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
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a method parameter or local variable.
	/// </summary>
	public sealed class VariableMetadata
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="name">The name of the variable.</param>
		/// <param name="type">The type of the variable.</param>
		/// <param name="isParameter">A value indicating whether the variable is a parameter of the containing method.</param>
		public VariableMetadata(string name, Type type, bool isParameter)
		{
			Requires.NotNullOrWhitespace(name, () => name);
			Requires.NotNull(type, () => type);

			Name = name;
			Type = type;
			IsParameter = isParameter;
		}

		/// <summary>
		///     Gets a value indicating whether the variable is a parameter of the containing method.
		/// </summary>
		public bool IsParameter { get; private set; }

		/// <summary>
		///     Gets the name of the variable.
		/// </summary>
		public string Name { get; private set; }

		/// <summary>
		///     Gets the type of the variable.
		/// </summary>
		public Type Type { get; private set; }
	}
}