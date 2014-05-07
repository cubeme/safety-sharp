﻿// The MIT License (MIT)
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

namespace SafetySharp.Metamodel.Declarations
{
	using System;
	using System.Collections.Immutable;
	using System.Linq;
	using Modeling;
	using Statements;
	using Types;

	/// <summary>
	///     Represents the declaration of a method within a component or interface.
	/// </summary>
	partial class MethodDeclaration
	{
		/// <summary>
		///     The default implementation of the <see cref="Component.Update()" /> method that simply returns.
		/// </summary>
		public static readonly MethodDeclaration UpdateMethod =
			new MethodDeclaration(identifier: new Identifier("Update"),
								  body: BlockStatement.Empty,
								  returnType: TypeSymbol.Void,
								  parameters: ImmutableArray<ParameterDeclaration>.Empty);

		/// <summary>
		///     Returns a string that represents the current object.
		/// </summary>
		public override string ToString()
		{
			return String.Format("Method '{0} {1}({2})'", ReturnType, Identifier, String.Join(", ", Parameters.Select(p => p.ToString())));
		}
	}
}