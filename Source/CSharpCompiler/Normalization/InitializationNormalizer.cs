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

namespace SafetySharp.CSharpCompiler.Normalization
{
	using System;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;
	using Roslyn;

	/// <summary>
	///     Initializes all locally declared variables to their types' default values if no initializer is provided.
	/// 
	///     For instance:
	///     <code>
	///  		int x;
	///  		// becomes:
	///  		int x = default(int);
	///  		
	///  		bool x = false, y, z;
	///  		// becomes:
	///  		bool x = false, y = default(bool), z = default(bool);
	/// 	</code>
	/// </summary>
	public class InitializationNormalizer : CSharpNormalizer
	{
		/// <summary>
		///     Initializes a new instance.
		/// </summary>
		public InitializationNormalizer()
			: base(NormalizationScope.ComponentStatements)
		{
		}

		/// <summary>
		///     Initializes the declared variable to its type's default value, if the <paramref name="declarator" /> has no initializer.
		/// </summary>
		public override SyntaxNode VisitVariableDeclarator(VariableDeclaratorSyntax declarator)
		{
			if (declarator.Initializer != null)
				return declarator;

			var type = ((VariableDeclarationSyntax)declarator.Parent).Type;
			var initializer = SyntaxFactory.EqualsValueClause(SyntaxFactory.DefaultExpression(type));
			return declarator.WithInitializer(initializer).NormalizeWhitespace();
		}
	}
}