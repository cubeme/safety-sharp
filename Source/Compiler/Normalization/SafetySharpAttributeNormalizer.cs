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

namespace SafetySharp.Compiler.Normalization
{
	using System;
	using System.Text;
	using CompilerServices;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Roslyn;

	/// <summary>
	///     Adds the <see cref="SafetySharpAttribute" /> to the compilation.
	/// </summary>
	public sealed class SafetySharpAttributeNormalizer : Normalizer
	{
		/// <summary>
		///     The name of the resource that stores the embedded original S# assembly.
		/// </summary>
		public const string EmbeddedAssembly = "S# Assembly";

		/// <summary>
		///     Normalizes the <see cref="Compilation" />.
		/// </summary>
		protected override Compilation Normalize()
		{
			var code = String.Format("[assembly: {0}(\"{1}\")]", typeof(SafetySharpAttribute).FullName, EmbeddedAssembly);
			var syntaxTree = SyntaxFactory.ParseSyntaxTree(code, path: Guid.NewGuid().ToString(), encoding: Encoding.UTF8);

			return Compilation.AddSyntaxTrees(syntaxTree);
		}
	}
}