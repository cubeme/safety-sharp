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
	using System.Collections.Generic;
	using BoundTree;
	using Utilities;

	/// <summary>
	///     Represents the immutable metadata of a S# method's body.
	/// </summary>
	public sealed class MethodBodyMetadata
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		/// <param name="parameters">The metadata of the parameters declared by the method.</param>
		/// <param name="localVariables">The metadata of the local variables declared by the method.</param>
		/// <param name="body">The block statement representing the method's body.</param>
		public MethodBodyMetadata(IEnumerable<VariableMetadata> parameters, IEnumerable<VariableMetadata> localVariables, BlockStatement body)
		{
			Requires.NotNull(parameters, () => parameters);
			Requires.NotNull(localVariables, () => localVariables);
			Requires.NotNull(body, () => body);

			Parameters = parameters;
			LocalVariables = localVariables;
			Body = body;
		}

		/// <summary>
		///     Gets the metadata of the parameters declared by the method.
		/// </summary>
		public IEnumerable<VariableMetadata> Parameters { get; private set; }

		/// <summary>
		///     Gets the metadata of the local variables declared by the method.
		/// </summary>
		public IEnumerable<VariableMetadata> LocalVariables { get; private set; }

		/// <summary>
		///     Gets the block statement representing the method's body.
		/// </summary>
		public BlockStatement Body { get; private set; }
	}
}