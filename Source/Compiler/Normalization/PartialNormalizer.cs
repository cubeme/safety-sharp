﻿// The MIT License (MIT)
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
	using CSharp.Roslyn;
	using CSharp.Roslyn.Syntax;
	using Microsoft.CodeAnalysis;
	using Microsoft.CodeAnalysis.CSharp;
	using Microsoft.CodeAnalysis.CSharp.Syntax;

	/// <summary>
	///     Ensures that all class declarations are marked <c>partial</c> such that additionally generated code can be easily added
	///     without having to consider fixing up line information for debugging purposes.
	/// </summary>
	public sealed class PartialNormalizer : Normalizer
	{
		/// <summary>
		///     Normalizes the <paramref name="classDeclaration" />.
		/// </summary>
		public override SyntaxNode VisitClassDeclaration(ClassDeclarationSyntax classDeclaration)
		{
			classDeclaration = (ClassDeclarationSyntax)base.VisitClassDeclaration(classDeclaration);

			if (!classDeclaration.Modifiers.Any(SyntaxKind.PartialKeyword))
			{
				var partialKeyword = SyntaxFactory.Token(SyntaxKind.PartialKeyword).WithTrailingSpace();
				classDeclaration = classDeclaration.WithModifiers(classDeclaration.Modifiers.Add(partialKeyword));
			}

			return classDeclaration;
		}
	}
}