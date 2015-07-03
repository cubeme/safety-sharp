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

namespace SafetySharp.Transformation
{
	using System;

	/// <summary>
	///     Indicates which operations are performed on a variable.
	/// </summary>
	[Flags]
	internal enum VariableOperations
	{
		/// <summary>
		///     Indicates that the variable is neither read nor written.
		/// </summary>
		None = 0,

		/// <summary>
		///     Indicates that the variable is read, but not written.
		/// </summary>
		Read = 1,

		/// <summary>
		///     Indicates that the variable is written, but not read.
		/// </summary>
		Write = 2,
	}

	/// <summary>
	///     Provides convenience methods for working with <see cref="VariableOperations" />.
	/// </summary>
	internal static class VariableOperationsExtensions
	{
		/// <summary>
		///     Gets a value indicating whether the <see cref="VariableOperations.Read" /> flag is set in <paramref name="operations" />
		///     .
		/// </summary>
		/// <param name="operations">The set of operations that should be checked.</param>
		public static bool IsRead(this VariableOperations operations)
		{
			return (operations & VariableOperations.Read) == VariableOperations.Read;
		}

		/// <summary>
		///     Gets a value indicating whether the <see cref="VariableOperations.Write" /> flag is set in
		///     <paramref name="operations" />.
		/// </summary>
		/// <param name="operations">The set of operations that should be checked.</param>
		public static bool IsWritten(this VariableOperations operations)
		{
			return (operations & VariableOperations.Write) == VariableOperations.Write;
		}
	}
}