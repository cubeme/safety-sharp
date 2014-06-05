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

namespace SafetySharp.Modeling
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Utilities;

	/// <summary>
	///     Provides metadata about a compilation unit within a Safety Sharp modeling assembly.
	/// </summary>
	[AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true, Inherited = false)]
	[UsedImplicitly]
	public class ModelingCompilationUnitAttribute : Attribute
	{
		/// <summary>
		///     Initializes a new instance of the <see cref="ModelingCompilationUnitAttribute" /> type.
		/// </summary>
		/// <param name="syntaxTree">The C# syntax tree representing the compilation unit.</param>
		/// <param name="filePath">The path of the file the C# code for the compilation unit is stored in.</param>
		public ModelingCompilationUnitAttribute(string syntaxTree, string filePath)
		{
			Requires.NotNull(syntaxTree, () => syntaxTree);
			Requires.NotNull(filePath, () => filePath);

			SyntaxTree = SyntaxFactory.ParseSyntaxTree(syntaxTree, filePath);
		}

		/// <summary>
		///     Gets the syntax tree of the compilation unit.
		/// </summary>
		internal SyntaxTree SyntaxTree { get; private set; }
	}
}